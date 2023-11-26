
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 
// A growable mostly lock free (or lock-based) concurrent
// unordered_map using a hash table.  On a key type K and value type V
// it supports:
//
//   unordered_map<K,V,Hash=std::hash<K>,Equal=std::equal_to<K>>(n) :
//   constructor for table of size n
//
//   find(const K&) -> std::optional<V> : returns key if found, otherwise empty
//
//   insert(const K&, const V&) -> bool : if key not in the table it inserts the key
//   with the given value and returns true, otherwise does nothing and
//   returns false
//
//   remove(const K&) -> bool : if key is in the table it removes the entry
//   and returns true, otherwise it does nothing and returns false.
//
//   upsert(const K&, (const std::optional<V>&) -> V)) -> bool : if
//   key is in the table with value v then it calls the function (second argument)
//   with std::optional<V>(v), replaces the current value with the
//   returned value, and returns false.  Otherwise it calls the
//   function with std::nullopt and inserts the key into the table with the
//   returned value, and returns true.
//
//   size() -> long : returns the size of the table.  Not linearizable with
//   the other functions, and takes time proportional to the table size.
//
// Will grow if any bucket reaches a contant size.  Grows by some costant factor
// and growing is done incrementally--i.e. each update helps move a constant number
// of buckets.

// Implementation: Each bucket points to a structure (Node) containing
// an array of entries.  Nodes come in varying sizes and on update the
// node is copied.   When growing each bucket is copied to k new buckets and the old
// bucket is marked as "forwarded".
//
// Define USE_LOCKS to use locks.  The lock-based version only
// acquires locks on updates.  Locks are faster with high contention
// workloads that include reads.  The non-lock version is marginally
// faster on low-contention uniform workloads, or if updates only.
// Also the lock-based version can suffer under oversubscription (more
// user threads than available hardware threads).
//
// The non-lock version still can block in two circumstances
//   - when allocating a new large array (the OS might block anyway)
//   - when copying a chunk of buckets (64) others block on just those buckets
// Otherwise updates are lock-free
//
// The type for keys and values must be copyable, and might be copied
// by the hash_table even when not being updated (e.g. when another
// key in the same bucket is being updated). 
//
// The upsert operation takes a function f of type
//   (const std::optional<V>&) -> V
// If using locks, f is executed with no write-write races.
// There can be concurrent reads on the old value, hence the const to prevent
// any read-write races.

#ifndef PARLAYHASH_H_
#define PARLAYHASH_H_

#include <atomic>
#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include <parlay/delayed.h>
#include "utils/epoch.h"
#include "utils/lock.h"
//#define USE_LOCKS 1

namespace parlay {

template <typename K,
	  typename V,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_map {

private:
  // set to grow by factor of 8 (2^3)
  static constexpr int log_grow_factor = 3;
  static constexpr int grow_factor = 1 << log_grow_factor;

  // groups of block_size buckets are copied over by a single thread
  static constexpr int block_size = 64;

  // size of bucket that triggers growth
  //static constexpr int overflow_size = 12;

  using KV = std::pair<K,V>;

  struct link {
    KV element;
    link* next;
    link(KV element, link* next) : element(element), next(next) {}
  };

  static std::optional<V> find_in_list(link* nxt, const K& k) {
    while (nxt != nullptr && !KeyEqual{}(nxt->element.first, k))
      nxt = nxt->next;
    if (nxt == nullptr) return {};
    else return nxt->element.second;
  }

  static std::tuple<int, link*, link*> remove_from_list(link* nxt, const K& k) {
    if (nxt == nullptr) return std::tuple(0, nullptr, nullptr);
    else if (KeyEqual{}(nxt->element.first, k))
      return std::tuple(1, nxt->next, nxt); 
    else {
      auto [len, ptr, rptr] = remove_from_list(nxt->next, k);
      if (len == 0) return std::tuple(0, nullptr, nullptr);
      return std::tuple(len + 1, epoch::New<link>(nxt->element, ptr), rptr);
    }
  }

  template <typename F>
  static std::pair<int, link*> update_list(link* nxt, const K& k, const F& f) {
    if (nxt == nullptr) return std::pair(0, nullptr);
    else if (KeyEqual{}(nxt->element.first, k)) 
      return std::pair(1, epoch::New<link>(std::pair(k,f(nxt->element.second)), nxt->next));
    else {
      auto [len, ptr] = update_list(nxt->next, k, f);
      if (len == 0) return std::pair(len, ptr);
      return std::pair(len + 1, epoch::New<link>(nxt->element, ptr));
    }
  }
    
  static void retire_list(link* nxt, int n) {
    while (n > 0) {
      n--;
      link* tmp = nxt->next;
      epoch::Retire(nxt);
      nxt = tmp;
    }
  }

  static void retire_all_list(link* nxt) {
    while (nxt != nullptr) {
      link* tmp = nxt->next;
      epoch::Retire(nxt);
      nxt = tmp;
    }
  }

  static int list_length(link* nxt) {
    int len = 0;
    while (nxt != nullptr) {
      len++;
      nxt = nxt->next;
    }
    return len;
  }

  // *********************************************
  // The bucket and table structures
  // *********************************************

  // pointer in bucket includes length and flag if forwarded
  struct head_ptr {
    size_t ptr;
    static head_ptr forwarded_link() {return head_ptr(1ul);}
    bool is_forwarded() {return ptr == 1ul ;}
    link* get_ptr() {return (link*) (ptr & ((1ul << 48) - 1));}
    size_t size() {return ptr >> 48;}
    std::pair<link*, size_t> ptr_and_length() {return std::pair(get_ptr(), size());}
    head_ptr() : ptr(0) {}
    head_ptr(size_t ptr) : ptr(ptr) {}
    head_ptr(link* x, size_t len)  : ptr(((size_t) x) | len << 48) {}
    bool operator ==(const head_ptr h) {return ptr == h.ptr;}
  };
      
  // one bucket of a sequence of buckets
  using bucket = std::atomic<head_ptr>;

  // status of a block
  enum status : char {Empty, Working, Done};

  // a single version of the table
  // this can change as the table grows
  struct table_version {
    std::atomic<table_version*> next; // points to next version if created
    std::atomic<long> finished_block_count; //number of blocks finished copying
    long num_bits;  // log_2 of size
    size_t size; // number of buckets
    int overflow_size; // size of bucket to trigger next expansion
    parlay::sequence<bucket> buckets; // sequence of buckets
    parlay::sequence<std::atomic<status>> block_status; // status of each block while copying

    // the index is the highest num_bits of the 40-bit hash
    long get_index(const K& k) {
      return (Hash{}(k) >> (40 - num_bits))  & (size-1u);}

    bucket* get_bucket(const K& k) {
      return &buckets[get_index(k)]; }

    // initial table version, n indicating initial size
    table_version(long n) 
       : next(nullptr),
	 finished_block_count(0),
	 num_bits(1 + parlay::log2_up(std::max<long>(block_size, n))),
	 size(1ul << num_bits),
	 overflow_size(num_bits < 18 ? 9 : 12),
	 buckets(parlay::tabulate<std::atomic<head_ptr>>(size, [] (long i) {return head_ptr();})) {}

    // expanded table version copied from smaller version t
    table_version(table_version* t)
      : next(nullptr),
	finished_block_count(0),
	num_bits(t->num_bits + log_grow_factor),
	size(t->size * grow_factor),
	overflow_size(num_bits < 18 ? 9 : 12),
	buckets(parlay::sequence<std::atomic<head_ptr>>::uninitialized(size)),
	block_status(parlay::sequence<std::atomic<status>>(t->size/block_size)) {
      std::fill(block_status.begin(), block_status.end(), Empty);
    }
  };

  // the current table version
  // points to next larger table version if one exists
  std::atomic<table_version*> current_table_version;

  // called when table should be expanded (i.e. when some bucket is too large)
  // allocates a new table version and links the old one to it
  void expand_table(table_version* ht) {
    table_version* htt = current_table_version.load();
    if (htt->next == nullptr) {
      long n = ht->buckets.size();
      // if fail on lock, someone else is working on it, so skip
      get_locks().try_lock((long) ht, [&] {
	 if (ht->next == nullptr) {
	   ht->next = epoch::memory_pool<table_version>::New(ht);
	   //std::cout << "expand to: " << n * grow_factor << std::endl;
	 }
	 return true;});
    }
  }

  // copies key_value into a new table
  // note this is not thread safe...i.e. only this thread should be
  // updating the bucket corresponding to the key.
  static void copy_element(table_version* t, KV& key_value) {
    size_t idx = t->get_index(key_value.first);
    auto [ptr, len] = t->buckets[idx].load().ptr_and_length();
    t->buckets[idx] = head_ptr(epoch::New<link>(key_value, ptr), len + 1);
  }

  void copy_bucket_cas(table_version* t, table_version* next, long i) {
    long exp_start = i * grow_factor;
    // Clear grow_factor buckets in the next table to put them in.
    for (int j = exp_start; j < exp_start + grow_factor; j++)
      next->buckets[j] = head_ptr();
    // copy bucket to grow_factor new buckets in next table
    while (true) {
      head_ptr bucket = t->buckets[i].load();
      link* ptr = bucket.get_ptr();
      link* next_ptr = ptr;
      while (next_ptr != nullptr) {
	copy_element(next, next_ptr->element);
	next_ptr = next_ptr->next;
      }
      bool succeeded = t->buckets[i].compare_exchange_strong(bucket, head_ptr::forwarded_link());
      if (succeeded) {
	retire_all_list(ptr);
	break;
      }
      // If the cas failed then someone updated bucket in the meantime so need to retry.
      // Before retrying need to clear out already added buckets..
      for (int j = exp_start; j < exp_start + grow_factor; j++) {
	head_ptr bucket = next->buckets[j].load();
	next->buckets[j] = head_ptr();
	retire_all_list(bucket.get_ptr());
      }
    }
  }

  void copy_bucket_lock(table_version* t, table_version* next, long i) {
    long exp_start = i * grow_factor;
    bucket* bck = &(t->buckets[i]);
    while (!get_locks().try_lock((long) bck, [=] {
      // Clear grow_factor buckets in the next table to put them in.
      for (int j = exp_start; j < exp_start + grow_factor; j++)
        next->buckets[j] = head_ptr();
      head_ptr bucket = t->buckets[i].load();
      link* ptr = bucket.get_ptr();
      link* next_ptr = ptr;
      while (next_ptr != nullptr) {
	copy_element(next, next_ptr->element);
	next_ptr = next_ptr->next;
      }
      t->buckets[i] = head_ptr::forwarded_link();
      return true;}))
      for (volatile int i=0; i < 200; i++);
  }

  // If copying is enabled (i.e. next is not null), and if the the hash bucket
  // given by hashid is not already copied, tries to copy block_size buckets, including
  // that of hashid, to the next larger hash_table.
  void copy_if_needed(long hashid) {
    table_version* t = current_table_version.load();
    table_version* next = t->next.load();
    if (next != nullptr) {
      long block_num = hashid & (next->block_status.size() -1);
      status st = next->block_status[block_num];
      status old = Empty;
      if (st == Done) return;
      else if (st == Empty &&
	       next->block_status[block_num].compare_exchange_strong(old, Working)) {
	long start = block_num * block_size;
	// copy block_size buckets
	for (int i = start; i < start + block_size; i++) {
#ifndef USE_LOCKS
	  copy_bucket_cas(t, next, i);
#else
	  copy_bucket_lock(t, next, i);
#endif
	}
	assert(next->block_status[block_num] == Working);
	next->block_status[block_num] = Done;
	// if all blocks have been copied then can set hash_table to next
	// and retire the old table
	if (++next->finished_block_count == next->block_status.size()) {
	  current_table_version = next;
	  epoch::memory_pool<table_version>::Retire(t);
	}
      } else {
	// If working then wait until Done
	while (next->block_status[block_num] == Working) {
	  for (volatile int i=0; i < 100; i++);
	}
      }
    }
  }

  // *********************************************
  // The internal find and update functions (find, insert, upsert and remove)
  // *********************************************

  std::optional<V> find_at(table_version* t, bucket* s, const K& k) {
    head_ptr x = s->load();
    if (x.is_forwarded()) {
      table_version* nxt = t->next.load();
      return find_at(nxt, nxt->get_bucket(k), k);
    }
    if (x.size() == 0) return std::optional<V>();
    return find_in_list(x.get_ptr(), k);
  }

  static bool weak_cas(bucket* s, head_ptr old_v, head_ptr new_v) {
#ifndef USE_LOCKS
    return (s->load() == old_v && s->compare_exchange_weak(old_v, new_v));
#else  // use try_lock
    return (get_locks().try_lock((long) s, [=] {
	       if (!(s->load() == old_v)) return false;
	       *s = new_v;
	       return true;}));
#endif
  }

  static void get_active_bucket(table_version* &t, bucket* &s, const K& k, head_ptr &old_node) {
    while (old_node.is_forwarded()) {
      t = t->next.load();
      s = t->get_bucket(k);
      old_node = s->load();
    }
  }

  std::optional<std::optional<V>>
  try_insert_at(table_version* t, bucket* s, const K& k, const V& v) {
    head_ptr old_head = s->load();
    get_active_bucket(t, s, k, old_head);
    auto [ptr, len] = old_head.ptr_and_length();
    if (len > t->overflow_size) expand_table(t);
    auto x = (len == 0) ? std::nullopt : find_in_list(ptr, k);
    if (x.has_value()) return std::optional<std::optional<V>>(x);
    link* new_ptr = epoch::New<link>(std::pair(k,v), ptr);
    head_ptr new_head = head_ptr(new_ptr, len + 1);
    if (weak_cas(s, old_head, new_head))
      return std::optional(std::optional<V>());
    epoch::Delete(new_ptr);
    return {};
  }

  template <typename F>
  static std::optional<bool> try_upsert_at(table_version* t, bucket* s, const K& k, F& f) {
    head_ptr old_head = s->load();
    get_active_bucket(t, s, k, old_head);
    auto [old_ptr, len] = old_head.ptr_and_length();
#ifndef USE_LOCKS
    auto [cnt, new_ptr] = update_list(old_ptr, k, f);
    if (cnt == 0) {
      new_ptr = epoch::New<link>(std::pair(k, f(std::optional<V>())), old_ptr);
      if (weak_cas(s, old_head, head_ptr(new_ptr, len + 1)))
	return true;
      epoch::Delete(new_ptr);
    } else {
      if (weak_cas(s, old_head, head_ptr(new_ptr, len))) {
	retire_list(old_ptr, cnt);
	return false;
      }
      retire_list(new_ptr, cnt);
    }
#else  // use try_lock
    if (!find_in_list(old_ptr, k).has_value()) {
      link* new_ptr = epoch::New<link>(std::pair(k, f(std::optional<V>())), old_ptr);
      if (weak_cas(s, old_head, head_ptr(new_ptr, len + 1))) return true;
      epoch::Delete(new_ptr);
    } else {
      if (get_locks().try_lock((long) s, [=] {
	  if (!(s->load() == old_head)) return false;
	  auto [cnt, new_ptr] = update_list(old_ptr, k, f);
	  *s = head_ptr(new_ptr, len);
	  retire_list(old_ptr, cnt);
	  return true;}))
	return false;
    }
#endif
    return {};
  }

  static std::optional<std::optional<V>> try_remove_at(table_version* t, bucket* s, const K& k) {
    head_ptr old_head = s->load();
    get_active_bucket(t, s, k, old_head);
    auto [old_ptr, len] = old_head.ptr_and_length();
    if (len == 0) return std::optional(std::optional<V>());
    auto [cnt, new_ptr, val_ptr] = remove_from_list(old_ptr, k);
    if (cnt == 0) return std::optional(std::optional<V>());
    if (weak_cas(s, old_head, head_ptr(new_ptr, len - 1))) {
      retire_list(old_ptr, cnt);
      return std::optional(std::optional<V>(val_ptr->element.second));
    }
    retire_list(new_ptr, cnt - 1);
    return {};
  }

  // forces all buckets to be copied to next table
  void force_copy() {
    table_version* ht = current_table_version.load();
    while (ht->next != nullptr) {
      for (int i=0; i < ht->size; i++)
	copy_if_needed(i);
      ht = current_table_version.load();
    }
  }

public:
  // *********************************************
  // The public interface
  // *********************************************

  unordered_map(long n) : current_table_version(epoch::New<table_version>(n)) {}

  ~unordered_map() {
    auto& buckets = current_table_version.load()->buckets;
    parlay::parallel_for (0, buckets.size(), [&] (size_t i) {
       head_ptr h= buckets[i].load();
       if (!h.is_forwarded()) 
	 retire_all_list(h.get_ptr());});
    epoch::memory_pool<table_version>::Retire(current_table_version.load());
  }

  std::optional<V> find(const K& k) {
    table_version* ht = current_table_version.load();
    bucket* s = ht->get_bucket(k);
    __builtin_prefetch (s);
    return epoch::with_epoch([=] {return find_at(ht, s, k);});
  }

  bool insert(const K& k, const V& v) {
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(k);
    bucket* s = &ht->buckets[idx];
    __builtin_prefetch (s);
    return epoch::with_epoch([=] {
      auto y = parlay::try_loop([=] {
	  copy_if_needed(idx);
          return try_insert_at(ht, s, k, v);});
      return !y.has_value();});
  }

  template <typename F>
  bool upsert(const K& k, const F& f) {
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(k);
    bucket* s = &ht->buckets[idx];
    __builtin_prefetch (s);
    return epoch::with_epoch([=] {
      return parlay::try_loop([=] {
          copy_if_needed(idx); // checks if table needs to grow
          return try_upsert_at(ht, s, k, f);});});
  }

  bool remove(const K& k) {
    table_version* ht = current_table_version.load();
    bucket* s = ht->get_bucket(k);
    __builtin_prefetch (s);
    return epoch::with_epoch([=] {
      auto y = parlay::try_loop([=] {return try_remove_at(ht, s, k);});
      return y.has_value();});
  }

  long size() {
    force_copy();
    table_version* ht = current_table_version.load();
    auto& table = ht->buckets;
    auto s = parlay::tabulate(ht->size, [&] (size_t i) {
	return table[i].load().size();});
    return parlay::reduce(s);
  }

  parlay::sequence<KV> entries() {
    force_copy();
    table_version* ht = current_table_version.load();
    auto& table = ht->buckets;
    auto s = epoch::with_epoch([&] {
    	       return parlay::tabulate(ht->size(), [&] (size_t i) {
		   link* ptr = table[i].load().get_ptr();
		   parlay::sequence<KV> r;
		   while (ptr != nullptr) {
		     r.push_back(ptr->element);
		     ptr = ptr->next;
		   }
		   return r;
		 });});
    return parlay::flatten(s);
  }
};

} // namespace parlay
#endif //PARLAYHASH_GROW_H_
