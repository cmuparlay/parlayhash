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

// Implementation: Each bucket points to a "functional" unsorted linked list of entries.
// In particular the links are immutable.
// On insertions of a new key it is added as a new link to the front of the list.
// On removal or update of an element, all elements up to the removed or updated
// element are copied.
// When growing, each bucket is copied to k new buckets and the old
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
#include "../parlay/primitives.h"
#include "../parlay/sequence.h"
#include "../parlay/delayed.h"
#include "../utils/epoch.h"
#include "../utils/lock.h"

//#define USE_LOCKS 1

namespace parlay {

template <typename K,
	  typename V,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_map {

private:
  // set to grow by factor of 8 (2^3) each time table expands
  static constexpr int log_grow_factor = 3;
  static constexpr int grow_factor = 1 << log_grow_factor;

  // groups of block_size buckets are copied to next larger table by a single thread
  static constexpr int block_size = 64;

  using KV = std::pair<K,V>;

  // Can be used to clear out epoch memory pool at end
  static constexpr bool default_clear_at_end = false;
  bool clear_memory_and_scheduler_at_end;
  parlay::internal::scheduler_type* sched_ref;

  // *********************************************
  // Linked lists used for each bucket
  // *********************************************
  
  struct link {
    KV element;
    link* next;
    link(KV element, link* next) : element(element), next(next) {}
  };

  // Find key in list, return nullopt if not found
  static std::pair<std::optional<V>,long> find_in_list(link* nxt, const K& k) {
    long n = 0;
    while (nxt != nullptr && !KeyEqual{}(nxt->element.first, k)) {
      nxt = nxt->next;
      n++;
    }
    if (nxt == nullptr) return std::pair(std::nullopt, n);
    else return std::pair(nxt->element.second,0);
  }

  // Remove key from list using path copying (i.e. does not update any links, but copies
  // path up to the removed link).
  // Returns a triple consisting of the position of the key in the list (1 based),
  // the head of the new list with the key removed, and a pointer to the link with the key.
  // If the key is not found, returns (0, nullptr, nullptr).
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

  // Update element with a given key in a list.  Uses path copying.
  // Returns a pair consisting of the position of the key in the list (1 based), and
  // the head of the new list with the key updated.
  // If the key is not found, returns (0, nullptr).
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

  // retires the first n elements of a list
  static void retire_list(link* nxt, int n) {
    while (n > 0) {
      n--;
      link* tmp = nxt->next;
      epoch::Retire(nxt);
      nxt = tmp;
    }
  }

  // retires all elements of a list
  static void retire_all_list(link* nxt) {
    while (nxt != nullptr) {
      link* tmp = nxt->next;
      epoch::Retire(nxt);
      nxt = tmp;
    }
  }

  // name is self descritpive
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

  // The structure stored in each bucket.  It includes a pointer to
  // the first link of a bucket list or marker indicating bucket is forwarded.
  struct head_ptr {
    size_t ptr;
    static head_ptr forwarded_link() {return head_ptr(reinterpret_cast<link*>(1ul));}
    bool is_forwarded() {return ptr == 1ul ;}
    head_ptr(link* ptr) : ptr(reinterpret_cast<size_t>(ptr)) {}
    operator link*() {return reinterpret_cast<link*>(ptr);}
    bool operator ==(const head_ptr h) {return ptr == h.ptr;}
  };
      
  // one bucket of a sequence of buckets
  using bucket = std::atomic<head_ptr>;

  // status of a block
  enum status : char {Empty, Working, Done};

  // A single version of the table.
  // A version includes a sequence of "size" "buckets".
  // New versions are added as the hash table grows, and each holds a
  // pointer to the next larger version, if one exists.
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
	 buckets(parlay::tabulate<std::atomic<head_ptr>>(size, [] (long i) {return head_ptr(nullptr);})) {}

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

  // The first table version.  Used for cleanup.
  table_version* initial_table_version;

  // *********************************************
  // Functions for exanding the table
  // *********************************************
  
  // called when table should be expanded (i.e. when some bucket is too large)
  // allocates a new table version and links the old one to it
  void expand_table(table_version* ht) {
    table_version* htt = current_table_version.load();
    if (htt->next == nullptr) {
      long n = ht->buckets.size();
      // if fail on lock, someone else is working on it, so skip
      get_locks().try_lock((long) ht, [&] {
	 if (ht->next == nullptr) {
	   ht->next = new table_version(ht);
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
    link* ptr = t->buckets[idx].load();
    t->buckets[idx] = epoch::New<link>(key_value, ptr);
  }

  // copies a bucket into grow_factor new buckets.
  // This is the version if USE_LOCKS is not set.
  void copy_bucket_cas(table_version* t, table_version* next, long i) {
    long exp_start = i * grow_factor;
    // Clear grow_factor buckets in the next table to put them in.
    for (int j = exp_start; j < exp_start + grow_factor; j++)
      next->buckets[j] = nullptr;
    // copy bucket to grow_factor new buckets in next table
    while (true) {
      head_ptr bucket = t->buckets[i].load();
      link* ptr = bucket;
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
      // Should happen rarely
      // Before retrying need to clear out already added buckets..
      for (int j = exp_start; j < exp_start + grow_factor; j++) {
	head_ptr bucket = next->buckets[j].load();
	next->buckets[j] = nullptr;
	retire_all_list(bucket);
      }
    }
  }

  // copies a bucket into grow_factor new buckets.
  // This is the version if USE_LOCKS is set.
  void copy_bucket_lock(table_version* t, table_version* next, long i) {
    long exp_start = i * grow_factor;
    bucket* bck = &(t->buckets[i]);
    while (!get_locks().try_lock((long) bck, [=] {
      // Clear grow_factor buckets in the next table to put them in.
      for (int j = exp_start; j < exp_start + grow_factor; j++)
        next->buckets[j] = nullptr;
      link* next_ptr = t->buckets[i].load();
      while (next_ptr != nullptr) {
	copy_element(next, next_ptr->element);
	next_ptr = next_ptr->next;
      }
      t->buckets[i] = head_ptr::forwarded_link();
      return true;}))
      for (volatile int i=0; i < 200; i++);
  }

  // If copying is ongoing (i.e. next is not null), and if the the hash bucket
  // given by hashid is not already copied, tries to copy block_size buckets, including
  // that of hashid, to the next larger table version.
  void copy_if_needed(table_version* t, long hashid) {
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
	// if all blocks have been copied then can set current table to next.
	if (++next->finished_block_count == next->block_status.size()) {
	  current_table_version = next;
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
  // Operations for finding, inserting, upserting, and removing from a bucket.
  // *********************************************

  std::optional<V> find_in_bucket(table_version* t, bucket* s, const K& k) {
    head_ptr x = s->load();
    // if bucket is forwarded, go to next version
    if (x.is_forwarded()) {
      table_version* nxt = t->next.load();
      return find_in_bucket(nxt, nxt->get_bucket(k), k);
    }
    return find_in_list(x, k).first;
  }

  // If using locks, acts like std::compare_exchange_weak, i.e., can fail
  // even if old_v == s->load() since it uses a try lock.
  // If lock free, then will always succeed if equal
  static bool weak_cas(bucket* s, head_ptr old_v, head_ptr new_v) {
#ifndef USE_LOCKS
    return (s->load() == old_v && s->compare_exchange_strong(old_v, new_v));
#else  // use try_lock
    return (get_locks().try_lock((long) s, [=] {
	       if (!(s->load() == old_v)) return false;
	       *s = new_v;
	       return true;}));
#endif
  }

  // If bucket is forwarded looks in successive larger versions until
  // it finds one that is not forwarded.
  // Unlikely, but possible, to go more than one version.
  // Note that this side effects t, s and old_node.
  static void get_active_bucket(table_version* &t, bucket* &s, const K& k, head_ptr &old_node) {
    while (old_node.is_forwarded()) {
      t = t->next.load();
      s = t->get_bucket(k);
      old_node = s->load();
    }
  }

  std::optional<std::optional<V>>
  try_insert_to_bucket(table_version* t, bucket* s, const K& k, const V& v) {
    head_ptr old_head = s->load();
    get_active_bucket(t, s, k, old_head);
    link* old_ptr = old_head;
    auto [x, len] = find_in_list(old_ptr, k);
    if (len > t->overflow_size) expand_table(t);
    // if already in the hash map, then return the current value
    if (x.has_value()) return std::optional<std::optional<V>>(x);
    link* new_ptr = epoch::New<link>(std::pair(k,v), old_ptr);
    head_ptr new_head = new_ptr;
    if (weak_cas(s, old_head, new_head))
      // successfully inserted
      return std::optional(std::optional<V>());
    epoch::Delete(new_ptr);
    // try failed, return std::nullopt to indicate that need to try again
    return std::nullopt;
  }

  template <typename F>
  static std::optional<bool> try_upsert_bucket(table_version* t, bucket* s, const K& k, F& f) {
    head_ptr old_head = s->load();
    get_active_bucket(t, s, k, old_head);
    link* old_ptr = old_head;
#ifndef USE_LOCKS
    auto [cnt, new_ptr] = update_list(old_ptr, k, f);
    if (cnt == 0) { // not in bucket, so insert new element
      new_ptr = epoch::New<link>(std::pair(k, f(std::optional<V>())), old_ptr);
      if (weak_cas(s, old_head, head_ptr(new_ptr)))
	return true;
      epoch::Delete(new_ptr);
    } else { // use the updated list
      if (weak_cas(s, old_head, head_ptr(new_ptr))) {
	retire_list(old_ptr, cnt);
	return false;
      }
      retire_list(new_ptr, cnt);
    }
#else  // use try_lock
    // update_list must be in a lock, so we first check if an update needs to be done
    // at all so we can avoid the lock if not necessary (i.e. key is not in the list).
    if (!find_in_list(old_ptr, k).first.has_value()) {
      link* new_ptr = epoch::New<link>(std::pair(k, f(std::optional<V>())), old_ptr);
      if (weak_cas(s, old_head, head_ptr(new_ptr)))
	return std::optional(true); // try succeeded, returing that a new element is inserted
      epoch::Delete(new_ptr); // failed, so delete and try again
    } else {
      if (get_locks().try_lock((long) s, [=] {
	  if (!(s->load() == old_head)) return false;
	  // note that the invocation of f is inside the lock
	  auto [cnt, new_ptr] = update_list(old_ptr, k, f);
	  *s = head_ptr(new_ptr);
	  retire_list(old_ptr, cnt);
	  return true;}))
	return std::optional(false); // try succeeded, returning that no new element is inserted
    }
#endif
    // try failed, return std::nullopt to indicate that need to try again
    return std::nullopt;
  }

  static std::optional<std::optional<V>> try_remove_from_bucket(table_version* t, bucket* s, const K& k) {
    head_ptr old_head = s->load();
    get_active_bucket(t, s, k, old_head);
    link* old_ptr = old_head;
    // if list is empty, then return that no remove needs to be done
    if (old_ptr == nullptr) return std::optional(std::optional<V>());
    auto [cnt, new_ptr, val_ptr] = remove_from_list(old_ptr, k);
    // if list does not contain key, then return that no remove needs to be done
    if (cnt == 0) return std::optional(std::optional<V>());
    if (weak_cas(s, old_head, head_ptr(new_ptr))) {
      // remove succeeded, return value that was removed
      retire_list(old_ptr, cnt);
      return std::optional(std::optional<V>(val_ptr->element.second));
    }
    retire_list(new_ptr, cnt - 1);
    // try failed, return std::nullopt to indicate that need to try again
    return std::nullopt;
  }

  // Clear bucket i of table t, and any forwarded buckets
  void clear_bucket(table_version* t, long i) {
    head_ptr head = t->buckets[i].load();
    if (!head.is_forwarded())
      retire_all_list(head);
    else {
      table_version* next = t->next.load();
      for (int j = 0; j < grow_factor; j++)
	clear_bucket(next, grow_factor * i + j);
    }
  }

  // Return size of bucket i of table version t.
  // Needs to follow through to forwarded buckets to find size.
  long bucket_size(table_version* t, long i) {
    head_ptr head = t->buckets[i].load();
    if (!head.is_forwarded())
      return list_length(head);
    table_version* next = t->next.load();
    long sum = 0;
    for (int j = 0; j < grow_factor; j++)
      sum += bucket_size(next, grow_factor * i + j);
    return sum;
  }

  // Add all entries in bucket i of table version t to result.
  // Needs to follow through to forwarded buckets accumuate entries.
  void bucket_entries(table_version* t, long i, parlay::sequence<KV>& result) {
    head_ptr head = t->buckets[i].load();
    if (!head.is_forwarded()) {
      link* ptr = head;
      while (ptr != nullptr) {
	result.push_back(ptr->element);
	ptr = ptr->next;
      }
    } else {
      table_version* next = t->next.load();
      for (int j = 0; j < grow_factor; j++)
	bucket_entries(next, grow_factor * i + j, result);
    }
  }

public:
  // *********************************************
  // The public interface
  // *********************************************

  unordered_map(long n, bool clear_at_end = default_clear_at_end)
    : current_table_version(new table_version(n)),
      initial_table_version(current_table_version.load()),
      clear_memory_and_scheduler_at_end(clear_at_end),
      sched_ref(clear_at_end ? new parlay::internal::scheduler_type(std::thread::hardware_concurrency()) : nullptr)
  {}

  ~unordered_map() {
    table_version* ht = current_table_version.load();
    // clear all buckets in current and larger versions
    parlay::parallel_for (0, ht->size, [&] (size_t i) {
      clear_bucket(ht, i);});
    // go through and delete all table versions
    table_version* tv = initial_table_version;
    while (tv != nullptr) {
      table_version* tv_next = tv->next;
      delete tv;
      tv = tv_next;
    }
    if (clear_memory_and_scheduler_at_end) {
      epoch::memory_pool<link>::clear();
      delete sched_ref;
    }
  }

  std::optional<V> find(const K& k) {
    table_version* ht = current_table_version.load();
    bucket* s = ht->get_bucket(k);
    __builtin_prefetch (s);
    return epoch::with_epoch([=] {
      return find_in_bucket(ht, s, k);});
  }

  bool insert(const K& k, const V& v) {
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(k);
    bucket* s = &ht->buckets[idx];
    __builtin_prefetch (s);
    return epoch::with_epoch([=] {
      auto y = parlay::try_loop([=] {
	  copy_if_needed(ht, idx);
          return try_insert_to_bucket(ht, s, k, v);});
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
	  copy_if_needed(ht, idx);
          return try_upsert_bucket(ht, s, k, f);});});
  }

  bool remove(const K& k) {
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(k);
    bucket* s = &ht->buckets[idx];
    __builtin_prefetch (s);
    return epoch::with_epoch([=] {
      auto y = parlay::try_loop([=] {
	  copy_if_needed(ht, idx);
	  return try_remove_from_bucket(ht, s, k);});
      return y.has_value();});
  }

  // runs in parallel across the buckets
  long size() {
    return entries().size();
    table_version* t = current_table_version.load();
    return epoch::with_epoch([&] {
      // The delayed means the sequence of bucket sizes is not materialized
      auto s = parlay::delayed::tabulate(t->size, [&] (size_t i) {
	  return bucket_size(t, i);});
      return parlay::reduce(s);});
  }

  // runs in parallel across the buckets
  parlay::sequence<KV> entries() {
    table_version* t = current_table_version.load();
    return epoch::with_epoch([&] {
      auto s = parlay::tabulate(t->size, [&] (size_t i) {
        parlay::sequence<KV> r;
	bucket_entries(t, i, r);
	return r;});
      return parlay::flatten(s);});
  }
};

} // namespace parlay
#endif //PARLAYHASH_GROW_H_
