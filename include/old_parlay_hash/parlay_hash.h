#include <atomic>
#include <optional>
#include <functional>
#include "../parlay/primitives.h"
#include "../parlay/sequence.h"
#include "../parlay/delayed.h"
#include "../utils/epoch.h"
#include "../utils/lock.h"

#ifndef PARLAY_HASH_H_
#define PARLAY_HASH_H_

//#define USE_LOCKS 1

#include "buckets.h"

namespace parlay {

template <typename Entry>
struct parlay_hash {
  using K = typename Entry::Key;

private:
  // set to grow by factor of 8 (2^3)
  static constexpr int log_grow_factor = 3;
  static constexpr int grow_factor = 1 << log_grow_factor;

  // groups of block_size buckets are copied over by a single thread
  static constexpr long min_block_size = 16;
  
  static constexpr bool default_clear_at_end = false;

  // *********************************************
  // Buckect structure
  // *********************************************

  using bstruct = buckets_struct<Entry>;
  bstruct bcks;
  using bucket = typename bstruct::bucket;
  using state = typename bstruct::state;
  
  // *********************************************
  // The table structures
  // *********************************************

  // status of a block of buckets
  enum status : char {Empty, Initializing, Forwarding, Done};

  // A single version of the table.
  // A version includes a sequence of "size" "buckets".
  // New versions are added as the hash table grows, and each holds a
  // pointer to the next larger version, if one exists.
  struct table_version {
    std::atomic<table_version*> next; // points to next version if created
    std::atomic<long> finished_block_count; //number of blocks finished copying
    long num_bits;  // log_2 of size
    size_t size; // number of buckets
    long block_size;
    int overflow_size; // size of bucket to trigger next expansion
    sequence<bucket> buckets; // sequence of buckets
    sequence<std::atomic<status>> block_status; // status of each block while copying

    // the index is the highest num_bits of the 40-bit hash
    long get_index(const K& k) {
      return (Entry::hash(k) >> (40 - num_bits))  & (size-1u);}

    bucket* get_bucket(const K& k) {
      return &buckets[get_index(k)]; }

    // initial table version, n indicating initial size
    table_version(long n) 
       : next(nullptr),
	 finished_block_count(0),
	 num_bits(std::max<long>(parlay::log2_up(min_block_size),
				 parlay::log2_up(n) + 1)),
	 size(1ul << num_bits),
	 block_size(num_bits < 10 ? min_block_size : (num_bits < 16 ? 64 : 256)),
	 overflow_size(num_bits < 18 ? 9 : 12),
	 buckets(parlay::sequence<bucket>::uninitialized(size)) {
      parlay::parallel_for(0, size, [&] (long i) { bstruct::initialize(buckets[i]);});
    }

    // expanded table version copied from smaller version t
    table_version(table_version* t)
      : next(nullptr),
	finished_block_count(0),
	num_bits(t->num_bits + log_grow_factor),
	size(t->size * grow_factor),
	block_size(num_bits < 16 ? 32 : 256),
	overflow_size(num_bits < 18 ? 9 : 12),
	buckets(parlay::sequence<bucket>::uninitialized(size)),
	block_status(parlay::sequence<std::atomic<status>>(t->size/t->block_size))
    {
      //parlay::parallel_for(0, size, [&] (long i) { bstruct::initialize(buckets[i]);});
      //for (int i=0; i < size; i++) bstruct::initialize(buckets[i]);
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

  // Copies a bucket into grow_factor new buckets.
  // This is the version if USE_LOCKS is not set.
  bool copy_bucket(table_version* t, table_version* next, long i) {
    long exp_start = i * grow_factor;
    state bck = bcks.get_state(t->buckets[i]);
    if (bck.is_forwarded()) return false;
    while (bck.is_stable()) {
      if (bcks.try_mark_as_initializing(t->buckets[i], bck)) { 
	for (int j = exp_start; j < exp_start + grow_factor; j++)
	  bcks.initialize(next->buckets[j]); 
	bcks.mark_as_initialized(t->buckets[i], bck);
      }
      bck = bcks.get_state(t->buckets[i]);
    }
    while (bck.is_initializing())
      bck = bcks.get_state(t->buckets[i]);
    state tmp_buckets[grow_factor];
    for (auto& e : bck) {
      size_t idx = next->get_index(e.get_key()) & (grow_factor - 1);
      tmp_buckets[idx] = bcks.push_state(tmp_buckets[idx], e);
    }
    for (int j = 0; j < grow_factor; j++) {
      bcks.try_copy(next->buckets[exp_start + j], tmp_buckets[j]);
    }
    //if (bcks.get_state(t->buckets[i]).is_forwarded()) return true;
    // if (bcks.try_mark_as_forwarded(t->buckets[i], bck))
    //   if (++next->finished_bucket_count == t->size) {
    // 	//current_table_version = next;
    // 	std::cout << "expand bucket done: " << i << ", " << parlay::worker_id() << std::endl;
    // 	return true;
    //   }
    // return false;
    return bcks.try_mark_as_forwarded(t->buckets[i], bck);
  }

  // If copying is ongoing (i.e., next is not null), and if the the
  // hash bucket given by hashid is not already copied, tries to copy
  // the block_size buckets that containing hashid to the next larger
  // table version.
  void copy_if_needed(table_version* t, long hashid) {
    table_version* next = t->next.load();
    if (next != nullptr) {
      long block_num = hashid / t->block_size; // CONVERT TO A SHIFT
      long start = block_num * t->block_size;
      status e = Empty;
      if (next->block_status[block_num].load() == Empty &&
	  next->block_status[block_num].compare_exchange_strong(e, Done)) {
	for (int i = start; i < start + t->block_size; i++)
	  copy_bucket(t, next, i);

	// if all blocks have been copied then can set current table to next
	if (++next->finished_block_count == t->size/t->block_size) {
	  current_table_version = next;
	  std::cout << "expand done" << std::endl;
	}
      } else copy_bucket(t, next, hashid);
    }
  }

  // *********************************************
  // The internal find and update functions (find, insert, upsert and remove)
  // *********************************************

  Entry* find_in_bucket(table_version* t, bucket* s, const K& k) {
    state x = bcks.get_state(*s);
    //if bucket is forwarded, go to next version
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

  static constexpr auto identity = [] (const Entry& kv) {return kv;};

  // Add all entries in bucket i of table version t to result.
  // Needs to follow through to forwarded buckets accumuate entries.
  template <typename Seq, typename F = decltype(identity)>
  static void bucket_entries(table_version* t, long i, Seq& result,
			     const F& f = identity) {
    state head = bstruct::get_state(t->buckets[i]);
    if (!head.is_forwarded()) {
      for (auto& e : head) result.push_back(f(e));
    } else {
      table_version* next = t->next.load();
      for (int j = 0; j < grow_factor; j++)
	bucket_entries(next, grow_factor * i + j, result);
    }
  }

  parlay::internal::scheduler_type* sched_ref;
  bool clear_memory_and_scheduler_at_end;

public:
  // *********************************************
  // The public interface
  // *********************************************

  struct Iterator {
    std::vector<Entry> entries;
    Entry entry;
    table_version* t;
    int i;
    long bucket_num;
    bool single;
    bool end;
    Iterator(bool end) : t(nullptr), i(0), bucket_num(-2l), single(false), end(true) {}
    Iterator(table_version* t) :
      t(t), i(0), bucket_num(-1l), single(false), end(false) {
      get_next_bucket();
    }
    Iterator(Entry entry) : entry(entry), single(true), end(false) {}
    void get_next_bucket() {
      while (entries.size() == 0 && ++bucket_num < t->size)
	bucket_entries(t, bucket_num, entries);
      if (bucket_num == t->size) end = true;
    }
    Iterator& operator++() {
      if (single) end = true;
      else if (++i == entries.size()) {
	i = 0;
	entries.clear();
	get_next_bucket();
      }
      return *this;
    }
    Entry& operator*() {
      if (single) return entry;
      return entries[i];}
    bool operator!=(const Iterator& iterator) {
      return !(end ? iterator.end : (bucket_num == iterator.bucket_num &&
				     i == iterator.i));
    }
  };
  Iterator begin() { return Iterator(current_table_version.load());}
  Iterator end() { return Iterator(true);}

  parlay_hash(long n, bool clear_at_end = default_clear_at_end)
    : clear_memory_and_scheduler_at_end(clear_at_end),
      sched_ref(clear_at_end ? new parlay::internal::scheduler_type(std::thread::hardware_concurrency()) : nullptr),
      current_table_version(new table_version(n)),
      bcks(bstruct(clear_at_end)),
      initial_table_version(current_table_version.load())
  {}

  void clear() {
    table_version* ht = current_table_version.load();
    // clear all buckets in current and larger versions
    parlay::parallel_for (0, ht->size, [&] (size_t i) {
      clear_bucket(ht, i);});
  }
  
  ~parlay_hash() {
    clear();
    // go through and delete all table versions
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

  //template <typename F = std::identity>
  //auto Find(const K& k, const F& f = {}) {
  template <typename F = decltype(identity)>
  auto Find(const K& k, const F& f = identity) {
    using rtype = typename std::result_of<F(Entry)>::type;
    table_version* ht = current_table_version.load();
    bucket* s = ht->get_bucket(k);
    auto l = s->load();
    //if (l.is_stable()) abort();
    if (l.is_empty()) return std::optional<rtype>();
    //__builtin_prefetch (s);
    return epoch::with_epoch([=] () -> std::optional<rtype> {
			       Entry* r = find_in_bucket(ht, s, k);
			       if (r == nullptr) return {};
			       else return std::optional<rtype>(f(*r));
      });
  }

  Iterator find(const K& k) {
    auto r = Find(k, identity);
    if (!r.has_value()) return Iterator(true);
    return Iterator(*r);
  }

  template <typename F = decltype(identity)>
  auto Insert(const Entry& entry, const F& f = identity) {
    using rtype = typename std::result_of<F(Entry)>::type;
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(entry.get_key());
    bucket* s = &ht->buckets[idx];
    __builtin_prefetch (s);
    return epoch::with_epoch([&] {
       auto y = parlay::try_loop([&] {
	  copy_if_needed(ht, idx);
          auto [x, len] = bcks.try_insert(s, entry);
	  if (!x.has_value()) get_active_bucket(ht, s, entry.get_key());
	  else if (len > ht->overflow_size) expand_table(ht);
	  return x;});
       if (y == nullptr) return std::optional<rtype>();
       else return std::optional(f(*y));});
  }
  
  std::pair<Iterator,bool> insert(const Entry& entry) {
    auto r = Insert(entry, identity);
    if (!r.has_value())
      return std::pair(Iterator(entry),true);
    return std::pair(Iterator(*r),false);
  }

  template <typename F>
  bool upsert(const K& k, const F& f) {
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(k);
    bucket* s = &ht->buckets[idx];
    __builtin_prefetch (s);
    return epoch::with_epoch([&] {
      return parlay::try_loop([&] {
  	  copy_if_needed(ht, idx); 
	  auto [x, len] = bcks.try_upsert(s, k, f);
	  if (!x.has_value())
	    get_active_bucket(ht, s, k);
	  else if (len > ht->overflow_size) expand_table(ht);
	  return x;});});
  }

  template <typename F = decltype(identity)>
  auto Remove(const K& k, const F& f = identity) {
    using rtype = typename std::result_of<F(Entry)>::type;
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(k);
    bucket* s = &ht->buckets[idx];
    __builtin_prefetch (s);
    return epoch::with_epoch([&] () -> std::optional<rtype> {
      auto y = parlay::try_loop([&] {
	  copy_if_needed(ht, idx);
	  auto x = bcks.try_remove(s, k);
	  if (!x.has_value()) 
	    get_active_bucket(ht, s, k);
	  return x;});
      if (y != nullptr) return std::optional(f(*y));
      else return {};});
  }

  Iterator erase(Iterator pos) {
    Remove(*pos.first);
    return Iterator(true);
  }

  long size() {
    table_version* t = current_table_version.load();
    return epoch::with_epoch([&] {
      auto s = parlay::tabulate(t->size, [&] (size_t i) {
	  return bucket_size(t, i);});
      return parlay::reduce(s);});
  }

  template <typename F = decltype(identity)>
  auto entries(const F& f = identity) {
    table_version* t = current_table_version.load();
    return epoch::with_epoch([&] {
      auto s = parlay::tabulate(t->size, [&] (size_t i) {
        parlay::sequence<Entry> r;
	bucket_entries(t, i, r, f);
	return r;});
      return flatten(s);});
  }
};

}
#endif // PARLAY_HASH_H_
