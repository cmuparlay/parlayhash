#ifndef PARLAY_HASH_H_
#define PARLAY_HASH_H_

#include <functional>
#include <optional>
#define PARLAY_USE_STD_ALLOC 1
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include <utils/epoch.h>
#include "bigatomic.h"

constexpr bool PrintGrow = true;

namespace parlay {

template <typename Entry>
struct parlay_hash {
  using K = typename Entry::Key;

  // *********************************************
  // Various parameters
  // *********************************************
  
  // set to grow by factor of 8 (2^3)
  static constexpr int log_grow_factor = 2;
  static constexpr int grow_factor = 1 << log_grow_factor;

  // groups of block_size buckets are copied over by a single thread
  // the block size typically grows with size, but starts here
  static constexpr long min_block_size = 4;

  // buffer_size is picked so state fits in a cache line (if it can)
  static constexpr long buffer_size = (sizeof(Entry) > 24) ? 1 : 48 / sizeof(Entry);

  // log_2 of the expected number of entries in a bucket (<= buffer_size)
  static constexpr long log_bucket_size =
    (buffer_size == 1) ? 0 : ((buffer_size == 2) ? 1 : ((buffer_size <= 4) ? 2 : 3));

  static long get_block_size(int num_bits) {
    return num_bits < 16 ? 16 : 256; }

  // The size of a bucket that causes the table to grow, i.e. if any
  // insert causes the bucket to reach the given size, then start
  // growing.
  // Technically this should be something like c log (n) / log(log n))
  // for a small constant c if each bucket is expected to hold 1
  // element, but.... each bucket can be expected to hold more than one.
  static long get_overflow_size(int num_bits) {
    if constexpr (log_bucket_size == 0) return num_bits < 18 ? 12 : 16;
    else if constexpr (log_bucket_size == 1) return num_bits < 18 ? 16 : 20;
    else if constexpr (log_bucket_size == 2) return num_bits < 18 ? 18 : 26;
    else return num_bits < 18 ? 22 : 30;
  }

  // clear_at_end will cause the scheduler and epoch-based collector
  // to clear their state on destruction
  static constexpr bool default_clear_at_end = false;
  bool clear_memory_and_scheduler_at_end;

  // a reference to the scheduler (null if not to be cleared)
  parlay::internal::scheduler_type* sched_ref;

  // *********************************************
  // The state structure for each bucket
  // *********************************************
  
  // for overflow lists for each bucket
  struct link {
    Entry entry;
    link* next;
    link(const Entry& entry, link* next) : entry(entry), next(next) { }
  };

  // for delayed reclamation of links using an epoch-based collector
  epoch::memory_pool<link>* link_pool;

  link* new_link(const Entry& entry, link* l) {
    return link_pool->New(entry, l); }
  void retire_link(link* l) { link_pool->Retire(l);}

  // Each bucket contains a "state", which consists of a fixed size
  // buffer of entries (buffer_size) and an overflow list.  The first
  // buffer_size entries in the bucket are kept in the buffer, and any
  // overflow goes to the list.  The head stores both the pointer to
  // the overflow list (lower 56 bits) and the number of elements in
  // the buffer, or buffer_size+1 if overfull (top 8 bits).
  struct state {
  public:
    size_t list_head;
    Entry buffer[buffer_size];
    state() : list_head(0) {}
    state(const Entry& e) : list_head(1ul << 48) {
      buffer[0] = e;
    }
    static constexpr size_t forwarded_val = 1ul;
    
    size_t make_head(link* l, size_t bsize) {
      return (((size_t) l) | (bsize << 48)); }

    // update overflow list with new ptr (assumes buffer is full)
    state(const state& s, link* ptr)
      : list_head(make_head(ptr, buffer_size + (ptr != nullptr))) {
      for (int i=0; i < buffer_size; i++)
	buffer[i] = s.buffer[i];
    }

    // add entry to the bucket state (in buffer if fits, otherwise at head of overflow list)
    template <typename NL>
    state(const state& s, Entry e, const NL& new_link) {
      for (int i=0; i < std::min(s.buffer_cnt(), buffer_size); i++) 
	buffer[i] = s.buffer[i];
      if (s.buffer_cnt() < buffer_size) {
	buffer[s.buffer_cnt()] = e;
	list_head = make_head(nullptr, s.buffer_cnt() + 1);
      } else {
	link* l = new_link(e, s.overflow_list());
	list_head = make_head(l, buffer_size + 1);
      }
    }

    // add entry to buffer (assumes it fits) -- specialization of above
    state(const state& s, Entry e) : list_head(make_head(nullptr, s.buffer_cnt() + 1)) {
      for (int i=0; i < s.buffer_cnt(); i++) 
	buffer[i] = s.buffer[i];
      buffer[s.buffer_cnt()] = e;
    }

    // remove buffer entry j, replace with first from overflow list (assumes there is overflow)
    state(const state& s, link* ptr, int j)
      : list_head(make_head(ptr->next, buffer_size + (ptr->next != nullptr))) {
      for (int i=0; i < buffer_size; i++)
	buffer[i] = s.buffer[i];
      buffer[j] = Entry{ptr->entry};
    }

    // remove buffer entry j, replace with last entry in buffer (assumes no overflow)
    state(const state& s, int j) : list_head(make_head(nullptr, s.buffer_cnt() - 1)) {
      if (s.overflow_list() != nullptr) abort();
      for (int i=0; i < s.buffer_cnt(); i++)
	buffer[i] = s.buffer[i];
      buffer[j] = buffer[s.buffer_cnt() - 1];
    }

    state(bool x) : list_head(forwarded_val) {}
    
    bool is_forwarded() const {return list_head == forwarded_val ;}

    // number of entries in buffer, or buffer_size+1 if overflow
    long buffer_cnt() const {return (list_head >> 48) & 255ul ;}

    // number of entries in bucket (includes those in the overflow list)
    long size() const {
      if (buffer_cnt() <= buffer_size) return buffer_cnt();
      return buffer_size + list_length(overflow_list());
    }

    // get the overflow list
    link* overflow_list() const {
      return (link*) (list_head & ((1ul << 48) - 1));}
  };

  // returns std::optional(f(entry)) for entry with given key
  template <typename F>
  static auto find_in_list(const link* nxt, const K& k, const F& f) {
    using rtype = typename std::result_of<F(Entry)>::type;
    long cnt = 0;
    while (nxt != nullptr && !nxt->entry.equal(k)) {
      nxt = nxt->next;
      cnt++;
    }
    if (nxt == nullptr)
      return std::pair(std::optional<rtype>(), cnt);
    else
      return std::pair(std::optional<rtype>(f(nxt->entry)), 0l);
  }

  // If k is found copies list elements up to k, and keeps the old
  // tail past k.  Returns the number of new nodes that will need to
  // be reclaimed, the head of the new list, and the link that is removed.
  // Returns [0, nullptr, nullptr] if k is not found
  std::tuple<int, link*, link*> remove_from_list(link* nxt, const K& k) {
    if (nxt == nullptr)
      return std::tuple(0, nullptr, nullptr);
    else if (nxt->entry.equal(k))
      return std::tuple(1, nxt->next, nxt);
    else {
      auto [len, ptr, removed] = remove_from_list(nxt->next, k);
      if (len == 0) return std::tuple(0, nullptr, nullptr);
      return std::tuple(len + 1, new_link(nxt->entry, ptr), removed);
    }
  }

  // retires first n elements of a list, but not the entries
  void retire_list_n(link* nxt, int n) {
    while (n > 0) {
      n--;
      link* tmp = nxt->next;
      retire_link(nxt);
      nxt = tmp;
    }
  }

  // Retires full list and their entries.  Used when destructing the
  // table.
  void retire_list_all(link* nxt) {
    while (nxt != nullptr) {
      link* tmp = nxt->next;
      nxt->entry.retire();
      retire_link(nxt);
      nxt = tmp;
    }
  }

  // Retires full list, but not their entries. Used when copying to a
  // new list during expansion, i.e. the entries will be in the new
  // list and don't need to be retired.
  void retire_list(link* nxt) {
    while (nxt != nullptr) {
      link* tmp = nxt->next;
      retire_link(nxt);
      nxt = tmp;
    }
  }

  static long list_length(link* nxt) {
    long len = 0;
    while (nxt != nullptr) {
      len++;
      nxt = nxt->next;
    }
    return len;
  }

  // Find key if it is in the buffer. Return index.
  int find_in_buffer(const state& s, const K& k) {
    long len = s.buffer_cnt();
    for (long i = 0; i < std::min(len, buffer_size); i++)
      if (s.buffer[i].equal(k))
	return i;
    return -1;
  }

  // Apply f to all entries in the state.
  template <typename F>
  void for_each_in_state(const state& s, const F& f) {
    for (long i = 0; i < std::min(s.buffer_cnt(), buffer_size); i++)
      f(s.buffer[i]);
    link* l = s.overflow_list();
    while (l != nullptr) {
      f(l->entry);
      l = l->next;
    }
  }
    
  // Find entry with given key if in the bucket (state).  Return
  // optional of f applied to the entry if found, otherwise
  // std::nullopt.
  template <typename F>
  auto find_in_state(const state& s, const K& k, const F& f)
    -> std::optional<typename std::result_of<F(Entry)>::type>
  {
    long len = s.buffer_cnt();
    for (long i = 0; i < std::min(len, buffer_size); i++)
      if (s.buffer[i].equal(k))
	return std::optional(f(s.buffer[i]));
    if (len <= buffer_size) return std::nullopt;
    return find_in_list(s.overflow_list(), k, f).first;
  }

  // A bucket is just an "atomic" state.
  // a big_atomic<x> is sort of like an std::atomic<x> but supports
  // load-linked, store-conditional, and is efficient when the x does
  // not fit in a machine word.
  using bckt = big_atomic<state>;

  // used for load-linked, store-conditionals
  using tag_type = typename big_atomic<state>::tag;

  // wrapper to ensure alignment
  struct alignas(64) bucket { bckt v; };

  // initialize an uninitialized bucket
  static void initialize(bucket& bck) {
    new (&bck.v) big_atomic<state>(state());
  }

  // *********************************************
  // The table structures
  // Each version increases in size, by grow_factor
  // *********************************************

  // status of a block of buckets, used when copying to a new version
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
    long block_size; // size of each block used for copying
    int overflow_size; // size of bucket to trigger next expansion
    bucket* buckets; // sequence of buckets
    //sequence<bucket> buckets; // sequence of buckets
    std::atomic<status>* block_status; // status of each block while copying

    // The index of a key is the highest num_bits of the lowest
    // 48-bits of the hash value.  Using the highest num_bits ensures
    // that when growing, a bucket will go to grow_factor contiguous
    // buckets in the next table.
    long get_index(const K& k) {
      return (Entry::hash(k) >> (48 - num_bits))  & (size-1u);}

    bckt* get_bucket(const K& k) {
      return &buckets[get_index(k)].v; }

    // initial table version, n indicating size
    table_version(long n) 
      : next(nullptr),
	finished_block_count(0),
	num_bits(std::max<long>(parlay::log2_up(min_block_size),
				(long) std::ceil(std::log2(1.5*n)) - log_bucket_size)),
	size(1ul << num_bits),
	block_size(num_bits < 10 ? min_block_size : get_block_size(num_bits)),
	overflow_size(get_overflow_size(num_bits))
	//buckets(parlay::sequence<bucket>::uninitialized(size)),
	//block_status(parlay::sequence<std::atomic<status>>(size/block_size)) 
    {
      if (PrintGrow) std::cout << "initial size: " << size << std::endl;
      buckets = (bucket*) malloc(sizeof(bucket)*size);
      block_status = (std::atomic<status>*) malloc(sizeof(std::atomic<status>) * size/block_size);
      parlay::parallel_for(0, size, [&] (long i) { initialize(buckets[i]);});
      parlay::parallel_for(0, size/block_size, [&] (long i) { block_status[i] = Empty;});
    }

    // expanded table version copied from smaller version t
    table_version(table_version* t)
      : next(nullptr),
	finished_block_count(0),
	num_bits(t->num_bits + log_grow_factor),
	size(t->size * grow_factor),
	block_size(get_block_size(num_bits)),
	overflow_size(get_overflow_size(num_bits))
	//buckets(parlay::sequence<bucket>::uninitialized(size)),
	//block_status(parlay::sequence<std::atomic<status>>::uninitialized(size/block_size))
    {
      buckets = (bucket*) malloc(sizeof(bucket)*size);
      block_status = (std::atomic<status>*) malloc(sizeof(std::atomic<status>) * size/block_size);
    }

    ~table_version() {
      free(buckets);
      free(block_status);
    }
  };

  // the current table version
  std::atomic<table_version*> current_table_version;

  // the initial table version, used for cleanup on destruction
  table_version* initial_table_version;

  // *********************************************
  // Functions for expanding the table
  // *********************************************

  // Called when table should be expanded (i.e. when some bucket is too large).
  // Allocates a new table version and links the old one to it.
  void expand_table(table_version* ht) {
    table_version* htt = current_table_version.load();
    if (htt->next == nullptr) {
      long n = ht->size;
      // if fail on lock, someone else is working on it, so skip
      get_locks().try_lock((long) ht, [&] {
	 if (ht->next == nullptr) {
	   ht->next = new table_version(ht);
	   if (PrintGrow)
	     std::cout << "expand to: " << n * grow_factor << std::endl;
	 }
	 return true;});
    }
  }

  // Copies a bucket into grow_factor new buckets.
  void copy_bucket(table_version* t, table_version* next, long i) {
    long exp_start = i * grow_factor;
    // Clear grow_factor buckets in the next table version to put them in.
    for (int j = exp_start; j < exp_start + grow_factor; j++)
      initialize(next->buckets[j]); 
    // copy bucket to grow_factor new buckets in next table version
    while (true) {
      // the bucket to copy
      auto [s, tag] = t->buckets[i].v.ll();

      // insert into grow_factor buckets (states) for next larger table
      state hold[grow_factor];
      size_t mask = grow_factor-1;
      for_each_in_state(s, [&] (const Entry& entry) {
	size_t idx = next->get_index(entry.get_key()) & mask;
       	hold[idx] = state(hold[idx], entry,
			  [&] (const Entry& e, link* l) {return new_link(e,l);});
      });

      // now store the buckets into table
      for (int j = 0; j < grow_factor; j++)
	next->buckets[grow_factor * i + j].v.store_sequential(hold[j]);

      // try to replace original bucket with forwarded marker
      if (t->buckets[i].v.sc(tag, state(true))) {
	retire_list(s.overflow_list()); 
	break;
      }
      
      // If the attempt failed then someone updated bucket in the meantime so need to retry.
      // Before retrying need to clear out already added buckets.
      for (int j = exp_start; j < exp_start + grow_factor; j++) {
	state ss = next->buckets[j].v.load();
	retire_list(ss.overflow_list());
	next->buckets[j].v.store_sequential(state());
      }
    }
  }

  // If copying is ongoing (i.e., next is not null), and if the the
  // hash bucket given by hashid is not already copied, tries to copy
  // the block_size buckets that containing hashid to the next larger
  // table version.
  void copy_if_needed(table_version* t, long hashid) {
    table_version* next = t->next.load();
    if (next != nullptr) {
      long num_blocks = t->size/t->block_size;
      long block_num = hashid & (num_blocks -1);
      status st = t->block_status[block_num];
      status old = Empty;
      if (st == Done) return;
      // This is effectively a try lock on the block_num.
      // It blocks other updates on the buckets associated with the block.
      else if (st == Empty &&
	       t->block_status[block_num].compare_exchange_strong(old, Working)) {

	// initialize block_status for next grow round
	for (int i = 0; i < grow_factor; i++)
	  next->block_status[grow_factor*block_num + i] = Empty;
	
	// copy block_size buckets
	long start = block_num * t->block_size;
	for (int i = start; i < start + t->block_size; i++) {
	  copy_bucket(t, next, i);
	}
	t->block_status[block_num] = Done;
	
	// If all blocks have been copied then can set current table
	// to next.  Note: this atomic fetch-and-add can be a
	// bottleneck and is the reason the block sizes are reasonably
	// large (e.g. 256).  A smarter combining tree could be used
	// if smaller block sizes are needed.
	if (++next->finished_block_count == num_blocks) {
	  //std::cout << "expand done" << std::endl;
	  current_table_version = next;
	}
      } else {
	// If another thread is working on the block, wait until Done
	while (t->block_status[block_num] == Working) {
	  for (volatile int i=0; i < 100; i++);
	}
      }
    }
  }
    
  // *********************************************
  // Construction and Destruction
  // *********************************************

  // Clear bucket, assuming it is not forwarded.
  void clear_bucket(bckt* b) {
    auto [s, tag] = b->ll();
    if (!s.is_forwarded() && b->sc(tag, state())) {
      for (int j=0; j < std::min(s.buffer_cnt(), buffer_size); j++) {
	s.buffer[j].retire();
      }
      retire_list_all(s.overflow_list());
    }
  }

  // Clears bucket or if the bucket is forwarded (during copying)
  // then clear the forwarded buckets.
  void clear_bucket_rec(table_version* t, long i) {
    bckt* b = &(t->buckets[i].v);
    state head = b->load();
    if (!head.is_forwarded())
      clear_bucket(b);
    else {
      table_version* next = t->next.load();
      for (int j = 0; j < grow_factor; j++)
	clear_bucket_rec(next, grow_factor * i + j);
    }
  }
  
  // Clear all memory.
  // Reinitialize to table of size 1 if specified, and by default.
  void clear(bool reinitialize = true) {
    table_version* ht = current_table_version.load();
    // clear buckets from current and future versions
    parlay::parallel_for (0, ht->size, [&] (size_t i) {
	clear_bucket_rec(ht, i);});

    // now reclaim the arrays
    table_version* tv = initial_table_version;
    while (tv != nullptr) {
      table_version* tv_next = tv->next;
      delete tv;
      tv = tv_next;
    }
    // reinitialize
    if (reinitialize) {
      current_table_version = new table_version(1);
      initial_table_version = current_table_version;
    }
  }

  // Creates initial table version for the given size.  The
  // clear_at_end allows to free up the epoch-based collector's
  // memory, and the scheduler.
  parlay_hash(long n, bool clear_at_end = default_clear_at_end)
    : clear_memory_and_scheduler_at_end(clear_at_end),
      sched_ref(clear_at_end ?
		new parlay::internal::scheduler_type(std::thread::hardware_concurrency()) :
		nullptr),
      link_pool(clear_at_end ?
		new epoch::memory_pool<link>() :
		&epoch::get_default_pool<link>()),
      current_table_version(new table_version(n)),
      initial_table_version(current_table_version.load())
  {}

  ~parlay_hash() {
    clear(false);
    if (clear_memory_and_scheduler_at_end) {
      delete sched_ref;
      delete link_pool;
    }
  }

  // *********************************************
  // Operations
  // *********************************************

  // Updates b, s, tag, and idx to the correct bucket, state, tag and
  // index if the the state s is forwarded.  Is called recursively,
  // but unlikely to go more than one level, and when not growing will
  // return immediately.
  void check_bucket_and_state(table_version* t, const K& k,
			      big_atomic<state>*& b, state& s, tag_type& tag, long& idx) {
    if (s.is_forwarded()) {
      table_version* nxt = t->next.load();
      idx = nxt->get_index(k);
      b = &(nxt->buckets[idx].v);
      std::tie(s, tag) = b->ll();
      check_bucket_and_state(nxt, k, b, s, tag, idx);
    }
  }

  // find in the bucket, or if forwarded (during copying) then follow
  // through to the next table, possibly reapeatedly, although
  // unlikely.
  template <typename F>
  auto find_in_bucket_rec(table_version* t, bckt* s, const K& k, const F& f)
    -> std::optional<typename std::result_of<F(Entry)>::type>
  {
    state x = s->load();
    //if bucket is forwarded, go to next version
    if (x.is_forwarded()) {
      table_version* nxt = t->next.load();
      return find_in_bucket_rec(nxt, nxt->get_bucket(k), k, f);
    }
    return find_in_state(x, k, f);
  }

  // Finds the entry with the key
  // Returns an optional which is empty if the key is not in the table,
  // and contains f(e) otherwise, where e is the entry matching the key
  // NOTE: this is the most important function to opmitize for performance
  // Hence one hand inline and one prefetch (not used anywhere else in code).
  template <typename F>
  auto Find(const K& k, const F& f)
    -> std::optional<typename std::result_of<F(Entry)>::type>
  {
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(k);
    bckt* b = &(ht->buckets[idx].v);
    // if entries are direct, then safe to scan the buffer without epoch protection
    if constexpr (Entry::Direct) {
      auto [s, tag] = b->ll();
      if (s.is_forwarded()) { // check_bucket_and_state inlined one level by hand
	table_version* nxt = ht->next.load();
	long idx = nxt->get_index(k);
	b = &(nxt->buckets[idx].v);
	std::tie(s, tag) = b->ll();
	check_bucket_and_state(nxt, k, b, s, tag, idx);
      }
      // search in buffer
      for (long i = 0; i < std::min(s.buffer_cnt(), buffer_size); i++)
	if (s.buffer[i].equal(k))
	  return std::optional(f(s.buffer[i]));
      // if not found and not overfull, then done
      if (s.buffer_cnt() <= buffer_size) return std::nullopt;
      // otherwise need to search overflow, which requires protection
      return epoch::with_epoch([&] {
        // if state has not changed, then just search list
	if (b->lv(tag)) return find_in_list(s.overflow_list(), k, f).first;
	return find_in_bucket_rec(ht, b, k, f);
      });
    } else { // if using indirection always use protection
      __builtin_prefetch(b); // allows read to be pipelined with epoch announcement
      return epoch::with_epoch([&] () -> std::optional<typename std::result_of<F(Entry)>::type> {
	  return find_in_bucket_rec(ht, b, k, f);});


    }
  }

  // Inserts at key, and does nothing if key already in the table.
  // The constr function construct the entry to be inserted if needed.
  // Returns an optional, which is empty if sucessfully inserted or
  // contains f(e) if not, where e is the entry matching the key.
  template <typename Constr, typename F>
  auto Insert(const K& key, const Constr& constr, const F& f)
    -> std::optional<typename std::result_of<F(Entry)>::type>
  {
    using rtype = std::optional<typename std::result_of<F(Entry)>::type>;
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(key);
    auto b = &(ht->buckets[idx].v);
    // if entries are direct, then safe to scan the buffer without epoch protection
    if constexpr (Entry::Direct) {
      auto [s, tag] = b->ll();
      copy_if_needed(ht, idx);
      check_bucket_and_state(ht, key, b, s, tag, idx);
      // if found in buffer then done
      for (long i = 0; i < std::min(s.buffer_cnt(), buffer_size); i++)
	if (s.buffer[i].equal(key)) return f(s.buffer[i]);
      if (s.buffer_cnt() < buffer_size) { // buffer has space, insert to end of buffer
	Entry entry = constr();
	if (b->sc(tag, state(s, entry))) return std::nullopt;
	entry.retire();
      }
    }
    // if indirect, or not found in buffer and buffer overfull then protect
    return epoch::with_epoch([&] () -> rtype {
      int delay = 200;
      while (true) {
	auto [s, tag] = b->ll();
	copy_if_needed(ht, idx);
	check_bucket_and_state(ht, key, b, s, tag, idx);
	long len = s.buffer_cnt();
	// if found in buffer then done
	for (long i = 0; i < std::min(len, buffer_size); i++)
	  if (s.buffer[i].equal(key)) return f(s.buffer[i]);
	if (len < buffer_size) { // buffer has space, insert to end of buffer
	  Entry new_e = constr();
	  if (b->sc(tag, state(s, new_e))) return std::nullopt;
	  new_e.retire(); // if failed need to ty again
	} else if (len == buffer_size) { // buffer full, insert new link
	  link* new_head = new_link(constr(), nullptr);
	  if (b->sc(tag, state(s, new_head))) 
	    return std::nullopt;
	  new_head->entry.retire(); // if failed need to ty again
	  retire_link(new_head);
	} else { // buffer overfull, need to check if in list
	  auto [x, list_len] = find_in_list(s.overflow_list(), key, f);
	  if (list_len + buffer_size > ht->overflow_size) expand_table(ht);
	  if (x.has_value()) return x; // if in list, then done
	  link* new_head = new_link(constr(), s.overflow_list());
	  if (b->sc(tag, state(s, new_head))) // try to add to head of list
	    return std::nullopt;
	  new_head->entry.retire(); // if failed need to ty again
	  retire_link(new_head);
	}
	// delay before trying again, only marginally helps
	for (volatile int i=0; i < delay; i++);
	delay = std::min(2*delay, 5000); // 1000-10000 are about equally good
      }
    });
  }

  // Removes entry with given key
  // Returns an optional which is empty if the key is not in the table,
  // and contains f(e) otherwise, where e is the entry that is removed.
  template <typename F>
  auto Remove(const K& key, const F& f)
    -> std::optional<typename std::result_of<F(Entry)>::type>
  {
    using rtype = std::optional<typename std::result_of<F(Entry)>::type>;
    table_version* ht = current_table_version.load();
    long idx = ht->get_index(key);
    auto b = &(ht->buckets[idx].v);
    // if entries are direct safe to scan the buffer without epoch protection
    if constexpr (Entry::Direct) {
      auto [s, tag] = b->ll();
      copy_if_needed(ht, idx);
      check_bucket_and_state(ht, key, b, s, tag, idx);
      if (s.buffer_cnt() <= buffer_size) {
	int i = find_in_buffer(s, key);
	if (i == -1) return std::nullopt;
	if (b->sc(tag, state(s, i))) {
	  rtype r = f(s.buffer[i]);
	  s.buffer[i].retire();
	  return r;
	} // if sc failed, will need to try again
      }
    }
    // if buffer overfull, or indirect, then need to protect
    return epoch::with_epoch([&] () -> rtype {
      int delay = 200;
      while (true) {
        auto [s, tag] = b->ll();
	copy_if_needed(ht, idx);
	check_bucket_and_state(ht, key, b, s, tag, idx);
	int i = find_in_buffer(s, key);
	if (i >= 0) { // found in buffer
	  if (s.buffer_cnt() > buffer_size) { // need to backfill from list
	    link* l = s.overflow_list();
	    if (b->sc(tag, state(s, l, i))) {
	      rtype r = f(s.buffer[i]);
	      s.buffer[i].retire();
	      retire_link(l);
	      return r;
	    } // if sc failed, will need to try again
	  } else { // buffer not overfull, can backfill within buffer
	    if (b->sc(tag, state(s, i))) {
	      rtype r = f(s.buffer[i]);
	      s.buffer[i].retire();
	      return r;
	    } // if sc failed, will need to try again
	  }
	} else { // not found in buffer
	  if (s.buffer_cnt() <= buffer_size) // if not overful, then done
	    return std::nullopt;
	  auto [cnt, new_list, removed] = remove_from_list(s.overflow_list(), key);
          if (cnt == 0) // if not found in list then done
	    return std::nullopt;
	  // if found, try to update with the new list that has the element removed
          if (b->sc(tag, state(s, new_list))) { 
	    rtype r = f(removed->entry); 
	    removed->entry.retire();
            retire_list_n(s.overflow_list(), cnt); // retire old list
            return r;
          } // if sc failed, will need to try again
          retire_list_n(new_list, cnt - 1); // failed, retire new list
	}
	for (volatile int i=0; i < delay; i++);
	delay = std::min(2*delay, 5000); // 1000-10000 are about equally good
      }
    });
  }

  // Size of bucket, or if forwarded, then sum sizes of all forwarded
  // buckets, recursively.
  long bucket_size_rec(table_version* t, long i) {
    state head = t->buckets[i].v.load();
    if (!head.is_forwarded())
      return  head.size();
    else {
      long sum = 0;
      table_version* next = t->next.load();
      for (int j = 0; j < grow_factor; j++)
	sum += bucket_size_rec(next, grow_factor * i + j);
      return sum;
    }
  }

  long size() {
    table_version* ht = current_table_version.load();
    //std::cout << std::endl;
    return epoch::with_epoch([&] {
      return parlay::reduce(parlay::tabulate(ht->size, [&] (size_t i) {
	    return bucket_size_rec(ht, i);}));});
  }

  // Apply function f to all entries in the given state 
  template <typename Seq, typename F>
  static void state_entries(state s, Seq& result, const F& f) {
    for_each_in_state(s, [&] (const Entry& entry) {
      result.push_back(f(entry));});
  }

  // Apply function f to entries of bucket i.  If bucket is forwarded
  // then follow through to all the forwarded buckets, recursively.
  template <typename Seq, typename F>
  static void bucket_entries_rec(table_version* t, long i, Seq& result, const F& f) {
    state s = t->buckets[i].v.load();
    if (!s.is_forwarded())
      state_entries(s, result, f);
    else {
      table_version* next = t->next.load();
      for (int j = 0; j < grow_factor; j++)
	bucket_entries_rec(next, grow_factor * i + j, result, f);
    }
  }

  // Apply function f to all entries of the table.  Works while updates are going on, and guarantees that:
  //   any element whose delete linearizes before the invocation will not be included
  //   any element whose insert linearizes after the response will not be included
  //   any element that is present from invocation to response will be included
  // Elements that are inserted or deleted between the invocation and response might or might not appear.
  template <typename F>
  parlay::sequence<Entry> entries(const F& f) {
    table_version* ht = current_table_version.load();
    return epoch::with_epoch([&] {
      auto s = parlay::tabulate(ht->size, [&] (size_t i) {
        parlay::sequence<Entry> r;
	bucket_entries_rec(ht, i, r, f);
	return r;});
      return flatten(s);});
  }

  // *********************************************
  // Iterator
  // *********************************************

  struct Iterator {
  public:
    using value_type        = typename Entry::Data;
    using iterator_category = std::forward_iterator_tag;
    using pointer           = value_type*;
    using reference         = value_type&;
    using difference_type   = long;

  private:
    std::vector<value_type> entries;
    value_type entry;
    table_version* t;
    int i;
    long bucket_num;
    bool single;
    bool end;
    void get_next_bucket() {
      while (entries.size() == 0 && ++bucket_num < t->size)
	bucket_entries(t, bucket_num, entries, [] (const Entry& e) {return e.get_entry();});
      if (bucket_num == t->size) end = true;
    }

  public:
    Iterator(bool end) : i(0), bucket_num(-2l), single(false), end(true) {}
    Iterator(table_version* t) : t(t),
      i(0), bucket_num(-1l), single(false), end(false) {
      get_next_bucket();
    }
    Iterator(value_type entry) : entry(entry), single(true), end(false) {}
    Iterator& operator++() {
      if (single) end = true;
      else if (++i == entries.size()) {
	i = 0;
	entries.clear();
	get_next_bucket();
      }
      return *this;
    }
    Iterator& operator++(int) {
      Iterator tmp = *this;
      if (single) end = true;
      else if (++i == entries.size()) {
	i = 0;
	entries.clear();
	get_next_bucket();
      }
      return tmp;
    }
    value_type& operator*() {
      if (single) return entry;
      return entries[i];}
    bool operator!=(const Iterator& iterator) {
      return !(end ? iterator.end : (bucket_num == iterator.bucket_num &&
				     i == iterator.i));
    }
    bool operator==(const Iterator& iterator) {
      return !(*this != iterator);}
  };

  Iterator begin() { return Iterator(current_table_version.load());}
  Iterator end() { return Iterator(true);}

  static constexpr auto identity = [] (const Entry& entry) {return entry;};
  static constexpr auto true_f = [] (const Entry& entry) {return true;};

  std::pair<Iterator,bool> insert(const Entry& entry) {
    auto r = Insert(entry, identity);
    if (!r.has_value())
      return std::pair(Iterator(entry),true);
    return std::pair(Iterator(*r),false);
  }

  Iterator erase(Iterator pos) {
    Remove(*pos.first, true_f);
    return Iterator(true);
  }

  size_t erase(const K& key) {
    return Remove(key, true_f).has_value();
  }

  Iterator find(const K& k) {
    auto r = Find(k, identity);
    if (!r.has_value()) return Iterator(true);
    return Iterator(*r);
  }

};

}  // namespace parlay
#endif  // PARLAY_HASH_H_
