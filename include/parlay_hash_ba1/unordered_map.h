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

#include "buckets.h"

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

  static constexpr bool default_clear_at_end = false;

  struct KV {
    using Key = K;
    using Value = V;
    K key;
    V value;
    bool equal(const K& k) const {return KeyEqual{}(key, k);}
    bool operator==(const KV& kv) const {return key == kv.key && value == kv.value;}
    bool operator!=(const KV& kv) const {return key != kv.key || value != kv.value;}
    const K& get_key() const {return key;}
    const V& get_value() const {return value;}
    KV(const K& k, const V& v) : key(k), value(v) {}
    KV() {}
  };
  
  // *********************************************
  // Buckect structure
  // *********************************************

  using bstruct = buckets_struct<KV>;
  bstruct bcks;
  using bucket = typename bstruct::bucket;
  using state = typename bstruct::state;
  
  // *********************************************
  // The table structures
  // *********************************************

  // status of a block of buckets
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
	 num_bits(parlay::log2_up(std::max<long>(block_size, n))),
	 size(1ul << num_bits),
	 overflow_size(40), //num_bits < 18 ? 9 : 12),
	 buckets(parlay::sequence<bucket>::uninitialized(size)) {
      parlay::parallel_for(0, size, [&] (long i) { bstruct::initialize(buckets[i]);});
    }

    // expanded table version copied from smaller version t
    table_version(table_version* t)
      : next(nullptr),
	finished_block_count(0),
	num_bits(t->num_bits + log_grow_factor),
	size(t->size * grow_factor),
	overflow_size(num_bits < 18 ? 9 : 12),
	buckets(parlay::sequence<bucket>::uninitialized(size)),
	block_status(parlay::sequence<std::atomic<status>>(t->size/block_size)) {
      std::fill(block_status.begin(), block_status.end(), Empty);
    }
  };

  // the current table version
  std::atomic<table_version*> current_table_version;

  // the initial table version, used for cleanup on destruction
  table_version* initial_table_version;

  // *********************************************
  // Functions for exanding the table
  // *********************************************

  // Called when table should be expanded (i.e. when some bucket is too large).
  // Allocates a new table version and links the old one to it.
  void expand_table(table_version* ht) {
    table_version* htt = current_table_version.load();
    if (htt->next == nullptr) {
      long n = ht->buckets.size();
      // if fail on lock, someone else is working on it, so skip
      get_locks().try_lock((long) ht, [&] {
	 if (ht->next == nullptr) {
	   ht->next = new table_version(ht);
	   std::cout << "expand to: " << n * grow_factor << std::endl;
	 }
	 return true;});
    }
  }

  // Copies a key_value pair into a new table version.
  // Note this is not thread safe...i.e. only this thread should be
  // updating the bucket corresponding to the key.
  void copy_element(table_version* t, KV& entry) {
    size_t idx = t->get_index(entry.get_key());
    bcks.push_entry(t->buckets[idx], entry);
  }

  // Copies a bucket into grow_factor new buckets.
  // This is the version if USE_LOCKS is not set.
  void copy_bucket_cas(table_version* t, table_version* next, long i) {
    long exp_start = i * grow_factor;
    // Clear grow_factor buckets in the next table version to put them in.
    for (int j = exp_start; j < exp_start + grow_factor; j++)
      bcks.initialize(next->buckets[j]);
    // copy bucket to grow_factor new buckets in next table version
    while (true) {
      state bck = bcks.get_state(t->buckets[i]);
      for (auto& e : bck)
	copy_element(next, e);

      // try to replace original bucket with forwarded marker
      // succeeded = t->buckets[i].compare_exchange_strong(bucket, head_ptr::forwarded_link());
      if (bcks.try_mark_as_forwarded(t->buckets[i], bck)) break;
	  
      // If the attempt failed then someone updated bucket in the meantime so need to retry.
      // Before retrying need to clear out already added buckets.
      for (int j = exp_start; j < exp_start + grow_factor; j++)
	bcks.clear(next->buckets[j]);
    }
  }

  // Copies a bucket into grow_factor new buckets.
  // This is the version if USE_LOCKS is set.
  void copy_bucket_lock(table_version* t, table_version* next, long i) {
    long exp_start = i * grow_factor;
    bucket* bck = &(t->buckets[i]);
    while (!get_locks().try_lock((long) bck, [=] {
      // Initialize grow_factor buckets in the next table version to put them in.
      for (int j = exp_start; j < exp_start + grow_factor; j++)
        bcks.initialize(next->buckets[j]);
      // copy to new buckets
      for (auto& e : get_state(t->buckets[i]))
	copy_element(next, e);
      // mark as forwarded
      bcks.mark_as_forwarded(t->buckets[i]);
      return true;}))
      for (volatile int i=0; i < 200; i++);
  }

  // If copying is ongoing (i.e., next is not null), and if the the
  // hash bucket given by hashid is not already copied, tries to copy
  // the block_size buckets that containing hashid to the next larger
  // table version.
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
	// if all blocks have been copied then can set current table to next
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
  // The internal find and update functions (find, insert, upsert and remove)
  // *********************************************

  std::optional<KV> find_in_bucket(table_version* t, bucket* s, const K& k) {
    state x = bcks.get_state(*s);
    // if bucket is forwarded, go to next version
    if (x.is_forwarded()) {
      table_version* nxt = t->next.load();
      return find_in_bucket(nxt, nxt->get_bucket(k), k);
    }
    return bcks.find(x, k);
  }

  static void get_active_bucket(table_version* &t, bucket* &s, const K& k) {
    while (s->load().is_forwarded()) {
      t = t->next.load();
      s = t->get_bucket(k);
    }
  }

  // Clear bucket i of table version t, and any forwarded buckets
  void clear_bucket(table_version* t, long i) {
    if (!bcks.get_state(t->buckets[i]).is_forwarded())
      bcks.clear(t->buckets[i]);
    else {
      table_version* next = t->next.load();
      for (int j = 0; j < grow_factor; j++)
	clear_bucket(next, grow_factor * i + j);
    }
  }

  // Return size of bucket i of table version t.
  // Needs to follow through to forwarded buckets to find size.
  long bucket_size(table_version* t, long i) {
    state head = bcks.get_state(t->buckets[i]);
    if (!head.is_forwarded())
      return bcks.length(head);
    table_version* next = t->next.load();
    long sum = 0;
    for (int j = 0; j < grow_factor; j++)
      sum += bucket_size(next, grow_factor * i + j);
    return sum;
  }

  // Add all entries in bucket i of table version t to result.
  // Needs to follow through to forwarded buckets accumuate entries.
  void bucket_entries(table_version* t, long i, parlay::sequence<KV>& result) {
    state head = bcks.get_state(t->buckets[i]);
    if (!head.is_forwarded()) {
      for (auto& e : head) result.push_back(e);
    } else {
      table_version* next = t->next.load();
      for (int j = 0; j < grow_factor; j++)
	bucket_entries(next, grow_factor * i + j, result);
    }
  }

  std::optional<V> strip_key(const std::optional<KV>& entry) {
    if (entry.has_value()) return std::optional((*entry).value);
    return std::nullopt;
  }
  
  parlay::internal::scheduler_type* sched_ref;
  bool clear_memory_and_scheduler_at_end;

public:
  // *********************************************
  // The public interface
  // *********************************************

  unordered_map(long n, bool clear_at_end = default_clear_at_end)
    : clear_memory_and_scheduler_at_end(clear_at_end),
      sched_ref(clear_at_end ? new parlay::internal::scheduler_type(std::thread::hardware_concurrency()) : nullptr),
      current_table_version(new table_version(n)),
      bcks(bstruct(clear_at_end)),
      initial_table_version(current_table_version.load())
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
      delete sched_ref;
    }
  }

  std::optional<V> find(const K& k) {
    table_version* ht = current_table_version.load();
    bucket* s = ht->get_bucket(k);
    state x = bcks.get_state(*s);
    if (!x.is_forwarded()) {
      if (x.length() == 0) return std::optional<V>();
      if (x.entry.equal(k)) return std::optional(x.entry.value);
      // long len = x.length();
      // for (long i = 0; i < std::min(len, bcks.block_size); i++)
      // 	if (x.entries[i].equal(k))
      // 	  return std::optional(x.entries[i].value);
      // if (len <= block_size) return std::optional<V>();
      //auto [y, flag] = bcks.fast_find(x, k);
      //if (flag) return strip_key(y);
    }
    //__builtin_prefetch (s);
    return epoch::with_epoch([=] {
       return strip_key(find_in_bucket(ht, s, k));});
  }

  bool insert(const K& k, const V& v) {
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(k);
    bucket* s = &ht->buckets[idx];
    __builtin_prefetch (s);
    return epoch::with_epoch([&] {
       auto y = parlay::try_loop([&] {
	  copy_if_needed(ht, idx);
          auto [x, len] = bcks.try_insert(s, KV(k, v));
	  if (!x.has_value()) get_active_bucket(ht, s, k);
	  else if (len > ht->overflow_size) expand_table(ht);
	  return x;});
       return !y.has_value();});
  }

  // template <typename F>
  // bool upsert(const K& k, const F& f) {
  //   table_version* ht = current_table_version.load();
  //   long idx = ht->get_index(k);
  //   bucket* s = &ht->buckets[idx];
  //   __builtin_prefetch (s);
  //   return epoch::with_epoch([=] {
  //     return parlay::try_loop([=] {
  // 	  copy_if_needed(ht, idx); // checks if table needs to grow
  //         return try_upsert_bucket(ht, s, k, f);});});
  // }

  template <typename F>
  bool upsert(const K& k, const F& f) {return false;}

  bool remove(const K& k) {
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(k);
    bucket* s = &ht->buckets[idx];
    __builtin_prefetch (s);
    return epoch::with_epoch([&] {
      auto y = parlay::try_loop([&] {
	  copy_if_needed(ht, idx);
	  auto x = bcks.try_remove(s, k);
	  if (!x.has_value()) 
	    get_active_bucket(ht, s, k);
	  return x;});
      //std::cout << "dsize: " << size() << ", " << y.has_value() << std::endl;
      return y.has_value();});
  }
		   
  long size() {
    table_version* t = current_table_version.load();
    return epoch::with_epoch([&] {
      auto s = parlay::tabulate(t->size, [&] (size_t i) {
	  return bucket_size(t, i);});
      return parlay::reduce(s);});
  }

  parlay::sequence<KV> entries() {
    table_version* t = current_table_version.load();
    return epoch::with_epoch([&] {
      auto s = parlay::tabulate(t->size, [&] (size_t i) {
        parlay::sequence<KV> r;
	bucket_entries(t, i, r);
	return r;});
      return flatten(s);});
  }
};

} // namespace parlay
#endif //PARLAYHASH_GROW_H_
