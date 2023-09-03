// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 
// A lock free (or lock-based) concurrent unordered_map using a hash
// table.   On a key type K and value type V it supports:
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
//   entries() -> parlay::sequence<std::pair<K,V>> : returns the
//   entries (key, value pairs) in the table.  Not linearizable with
//   the other functions, and takes time proportional to the table
//   size.
//
// Implementation: Each bucket points to a structure (Node) containing
// an array of entries.  Nodes come in varying sizes and on update the
// node is copied.  Allows arbitrary growing, but only efficient if
// not much larger than the original given size (i.e. number of
// buckets is fixed, but number of entries per bucket can grow).  Time
// is proportional to the size of the bucket.
//
// Define USE_LOCKS to use locks.  The lock-based version only
// acquires locks on updates.  Locks are faster with high contention
// workloads that include reads.  The lock-free version is marginally
// faster on low-contention uniform workloads, or if updates only.
// Also the lock-based version can suffer under oversubscription (more
// user threads than available hardware threads).
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
#include "epoch.h"
#include "lock.h"
#define USE_LOCKS 1

namespace parlay {
  
template <typename K,
	  typename V,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_map {
private:
  using KV = std::pair<K,V>;

  template <typename Range>
  static int find_in_range(const Range& entries, long cnt, const K& k) {
    for (int i=0; i < cnt; i++)
      if (KeyEqual{}(entries[i].first, k)) return i;
    return -1;
  }

  // The following three functions copy a range and
  // insert/update/remove the specified key.  No ordering is assumed
  // within the range.  Insert assumes k does not appear, while
  // update/remove assume it does appear at index idx.
  template <typename Range, typename RangeIn>
  static void copy_and_insert(Range& out, const RangeIn& entries, long cnt,
			      const K& k, const V& v) {
    assert(cnt >= 0);
    for (int i=0; i < cnt; i++) out[i] = entries[i];
    out[cnt] = KV{k,v};
  }

  template <typename Range, typename RangeIn, typename F>
  static void copy_and_update(Range& out, const RangeIn& entries, long cnt,
			      const K& k, const F& f, long idx) {
    assert(cnt > 0);
    for (int i = 0; i < idx; i++) out[i] = entries[i];
    out[idx].first = entries[idx].first;
    out[idx].second = f(entries[idx].second);
    for (int i = idx+1; i < cnt; i++) out[i] = entries[i];
  }

  template <typename Range, typename RangeIn>
  static void copy_and_remove(Range& out, const RangeIn& entries, long cnt, const K& k, long idx) {
    assert(cnt > 1);
    for (int i = 0; i < idx; i++) out[i] = entries[i];
    for (int i = idx; i < cnt-1; i++) out[i] = entries[i+1];
  }
  
  // Each bucket points to a Node of some Size, or to a BigNode (defined below)
  // A node contains an array of up to Size entries (actual # of entries given by cnt)
  // Sizes are 1, 3, 7, 31
  template <int Size>
  struct Node {
    using node = Node<0>;
    int cnt;
    KV entries[Size];

    KV* get_entries() {
      if (cnt < 31) return entries;
      else return ((BigNode*) this)->entries.begin();
    }

    // return index of key in entries, or -1 if not found
    int find_index(const K& k) {
      if (cnt <= 31) return find_in_range(entries, cnt, k);
      else return find_in_range(((BigNode*) this)->entries, cnt, k);
    }

    // return optional value found in entries given a key
    std::optional<V> find(const K& k) {
      if (cnt <= 31) { // regular node
	if (KeyEqual{}(entries[0].first, k)) // shortcut for common case
	   return entries[0].second;
	int i = find_in_range(entries+1, cnt-1, k);
	if (i == -1) return {};
	else return entries[i].second;
      } else { // big node
	int i = find_in_range(((BigNode*) this)->entries, cnt, k);
	if (i == -1) return {};
	else return ((BigNode*) this)->entries[i].second;
      }
    }

    // copy and insert
    Node(node* old, const K& k, const V& v) {
      cnt = (old == nullptr) ? 1 : old->cnt + 1;
      copy_and_insert(entries, old->entries, cnt-1, k, v);
    }

    // copy and update
    template <typename F>
    Node(long idx, node* old, const K& k, const F& f) : cnt(old->cnt) {
      assert(old != nullptr);
      copy_and_update(entries, old->entries, cnt, k, f, idx);
    }

    // copy and remove
    Node(long idx, node* old, const K& k) : cnt(old->cnt - 1) {
      if (cnt == 31) copy_and_remove(entries, ((BigNode*) old)->entries, cnt+1, k, idx);
      else copy_and_remove(entries, old->entries, cnt+1, k, idx);
    }

    Node(int cnt) : cnt(cnt) {}
  };
  using node = Node<0>;

  // If a node overflows (cnt > 31), then it becomes a big node and its content
  // is stored indirectly in an std::vector.
  struct BigNode {
    using entries_type = parlay::sequence<KV>;
    int cnt;
    entries_type entries;

    BigNode(node* old, const K& k, const V& v) : cnt(old->cnt + 1) {
      entries = parlay::tabulate(cnt, [] (long i) {return KV{};}, cnt);
      if (old->cnt == 31) copy_and_insert(entries, old->entries, old->cnt, k, v);
      else copy_and_insert(entries, ((BigNode*) old)->entries, old->cnt, k, v);
    }

    template <typename F>
    BigNode(long idx, node* old, const K& k, const F& f) : cnt(old->cnt) {
      entries = parlay::tabulate(cnt, [] (long i) {return KV{};}, cnt);
      copy_and_update(entries, ((BigNode*) old)->entries, cnt, k, f, idx);  }

    BigNode(long idx, node* old, const K& k) : cnt(old->cnt - 1) {
      entries = parlay::tabulate(cnt, [] (long i) {return KV{};}, cnt);
      copy_and_remove(entries, ((BigNode*) old)->entries, cnt+1, k, idx); }

    BigNode(int cnt) : cnt(cnt) {
      entries = parlay::tabulate(cnt, [] (long i) {return KV{};}, cnt);
    }

  };

  static node* insert_to_node(node* old, const K& k, const V& v) {
    if (old == nullptr) return (node*) epoch::memory_pool<Node<1>>::New(old, k, v);
    if (old->cnt < 3) return (node*) epoch::memory_pool<Node<3>>::New(old, k, v);
    else if (old->cnt < 7) return (node*) epoch::memory_pool<Node<7>>::New(old, k, v);
    else if (old->cnt < 31) return (node*) epoch::memory_pool<Node<31>>::New(old, k, v);
    else return (node*) epoch::memory_pool<BigNode>::New(old, k, v);
  }

  template <typename F>
  static node* update_node(node* old, const K& k, const F& f, long idx) {
    assert(old != nullptr);
    if (old == nullptr) return (node*) epoch::memory_pool<Node<1>>::New(idx, old, k, f);
    if (old->cnt < 3) return (node*) epoch::memory_pool<Node<3>>::New(idx, old, k, f);
    else if (old->cnt < 7) return (node*) epoch::memory_pool<Node<7>>::New(idx, old, k, f);
    else if (old->cnt < 31) return (node*) epoch::memory_pool<Node<31>>::New(idx,old, k, f);
    else return (node*) epoch::memory_pool<BigNode>::New(idx, old, k, f);
  }

  static node* remove_from_node(node* old, const K& k, long idx) {
    assert(old != nullptr);
    if (old->cnt == 1) return (node*) nullptr;
    if (old->cnt == 2) return (node*) epoch::memory_pool<Node<1>>::New(idx, old, k);
    else if (old->cnt <= 4) return (node*) epoch::memory_pool<Node<3>>::New(idx, old, k);
    else if (old->cnt <= 8) return (node*) epoch::memory_pool<Node<7>>::New(idx, old, k);
    else if (old->cnt <= 32) return (node*) epoch::memory_pool<Node<31>>::New(idx, old, k);
    else return (node*) epoch::memory_pool<BigNode>::New(idx, old, k);
  }

  static void retire_node(node* old) {
    if (old == nullptr);
    else if (old->cnt == 1) epoch::memory_pool<Node<1>>::Retire((Node<1>*) old);
    else if (old->cnt <= 3) epoch::memory_pool<Node<3>>::Retire((Node<3>*) old);
    else if (old->cnt <= 7) epoch::memory_pool<Node<7>>::Retire((Node<7>*) old);
    else if (old->cnt <= 31) epoch::memory_pool<Node<31>>::Retire((Node<31>*) old);
    else epoch::memory_pool<BigNode>::Retire((BigNode*) old);
  }

  static bool check_node(node* old) {
    if (old == nullptr) return true;
    else if (old->cnt == 1) return epoch::memory_pool<Node<1>>::check_not_corrupted((Node<1>*) old);
    else if (old->cnt <= 3) return epoch::memory_pool<Node<3>>::check_not_corrupted((Node<3>*) old);
    else if (old->cnt <= 7) return epoch::memory_pool<Node<7>>::check_not_corrupted((Node<7>*) old);
    else if (old->cnt <= 31) return epoch::memory_pool<Node<31>>::check_not_corrupted((Node<31>*) old);
    else return epoch::memory_pool<BigNode>::check_not_corrupted((BigNode*) old);
  }

  
  static node* allocate_node(int cnt) {
    if (cnt == 0) return nullptr;
    else if (cnt == 1) return (node*) epoch::memory_pool<Node<1>>::New(cnt);
    else if (cnt <= 3) return (node*) epoch::memory_pool<Node<3>>::New(cnt);
    else if (cnt <= 7) return (node*)epoch::memory_pool<Node<7>>::New(cnt);
    else if (cnt <= 31) return (node*) epoch::memory_pool<Node<31>>::New(cnt);
    else return (node*) epoch::memory_pool<BigNode>::New(cnt);
  }

  static void destruct_node(node* old) {
    if (old == nullptr);
    else if (old->cnt == 1) epoch::memory_pool<Node<1>>::Delete((Node<1>*) old);
    else if (old->cnt <= 3) epoch::memory_pool<Node<3>>::Delete((Node<3>*) old);
    else if (old->cnt <= 7) epoch::memory_pool<Node<7>>::Delete((Node<7>*) old);
    else if (old->cnt <= 31) epoch::memory_pool<Node<31>>::Delete((Node<31>*) old);
    else epoch::memory_pool<BigNode>::Delete((BigNode*) old);
  }

  // *********************************************
  // The bucket and table structures
  // *********************************************

  using vtype = long;
  
  static constexpr int mask_bits = 4;
  static constexpr vtype mask = (1l << mask_bits)-1l;
  static constexpr int num_cached = 3;
  static constexpr vtype busy_version = -1;

  static vtype next_version(vtype version) {
    return ((version >> mask_bits) + 1l) << mask_bits;
  }

  static int get_cnt(vtype version) {
    return (version & mask);
  }
  static bool is_busy(vtype v) {return v == busy_version;}
  static bool is_long(int cnt) {return cnt > num_cached;}

  // static node* mark_cached(node* x) {return (node*) (((vtype) x) | 1ul);}
  // static bool is_cached(node* x) {return ((vtype) x) & 1;}
  // static node* strip_cached(node* x) {return (node*) (((vtype) x) & ~1ul);}

  struct alignas(64) bucket {
    std::atomic<node*> ptr;
    std::atomic<vtype> version;
    KV keyval[num_cached];
    bucket() : ptr(nullptr), version(0) {}
  };

  struct Table {
    parlay::sequence<bucket> table;
    size_t size;
    bucket* get_bucket(const K& k) {
      size_t idx = Hash{}(k)  & (size-1u);
      return &(table[idx]);
    }
    Table(size_t n) {
      int bits = parlay::log2_up(n);
      size = 1ul << bits;
      table = parlay::sequence<bucket>(size);
    }
  };

  Table hash_table;

  // *********************************************
  // The internal update functions (insert, upsert and remove)
  // *********************************************

  // read a snapshot from the cache, and put in buffer
  // the snapshot is associated with a version
  struct cache_snapshot {
    char buffer[sizeof(KV)*num_cached];
    vtype version;
    KV* data() {return (KV*) buffer;}
    cache_snapshot(bucket* s) : version(s->version.load()) {
      if (!is_busy(version)) {
	int cnt = std::min(get_cnt(version), num_cached);
	memcpy(buffer, s->keyval, cnt*sizeof(KV));
	if (s->version.load() != version)
	  version = busy_version;
      }
    }
  };

  // load cache with values from new_node
  static void load_cache(bucket* s, node* new_node, unsigned int version) {
    if (new_node != nullptr) {
      s->version = busy_version;
      s->keyval[0] = new_node->entries[0];
      if (new_node->cnt == 1)
	s->version = version + 1;
      else {
	s->keyval[1] = new_node->entries[1];
	if (new_node->cnt == 2)
	  s->version = version + 2;
	else {
	  s->keyval[2] = new_node->entries[2];
	  if (new_node->cnt == 3)
	    s->version = version + 3;
	  else s->version = version + 4;
	}
      }
    } else s->version = version;
  }

  // try to install a new node in bucket s from an old_node
  static bool try_update(bucket* s, node* old_node, node* new_node) {
    if (get_locks().try_lock((long) s, [=] {
        if (s->ptr.load() != old_node) return false;
	unsigned int version = next_version(s->version.load());
	s->ptr = new_node;
	load_cache(s, new_node, version);
	return true;})) {
      if (new_node != nullptr && new_node->cnt <= num_cached)
	retire_node(new_node);
      if (old_node != nullptr && old_node->cnt > num_cached)
	retire_node(old_node);
      // retire_node(old_node);
      return true;
    }
    destruct_node(new_node);
    return false;
  }

  // try to install a new node in bucket s from an old_node
  static bool try_cached_update(bucket* s, vtype version, node* new_node) {
    if (get_locks().try_lock((long) s, [=] {
        if (s->version.load() != version) return false;
	unsigned int version = next_version(s->version.load());
	s->ptr = new_node;
	load_cache(s, new_node, version);
	return true;})) {
      if (new_node != nullptr && new_node->cnt <= num_cached)
	retire_node(new_node);
      return true;
    }
    destruct_node(new_node);
    return false;
  }

  static std::optional<std::optional<V>>
  try_insert_at(bucket* s, const K& k, const V& v) {
    node* old_node = s->ptr.load();
    auto x = (old_node == nullptr) ? std::nullopt : old_node->find(k);
    if (x.has_value()) return std::optional(x);
    if (try_update(s, old_node, insert_to_node(old_node, k, v)))
      return std::optional(std::optional<V>());
    else return {};
  }
  
  static std::optional<std::optional<V>>
  try_cached_insert_at(bucket* s, const K& k, const V& v) {
    cache_snapshot buffer(s);
    if (is_busy(buffer.version)) return {};
    int cnt = get_cnt(buffer.version);
    int idx = find_in_range(buffer.data(), std::min(cnt, num_cached), k);
    if (idx != -1) return std::optional(buffer.data()[idx].second);
    if (cnt > num_cached) return {};
    node* new_node = allocate_node(cnt+1);
    KV* values = new_node->get_entries();
    copy_and_insert(values, buffer.data(), cnt, k, v);
    if (try_cached_update(s, buffer.version, new_node))
      return std::optional(std::optional<V>());
    else return {};
  }

  static std::optional<std::optional<V>> try_remove_at(bucket* s, const K& k) {
    node* old_node = s->ptr.load();
    int i = (old_node == nullptr) ? -1 : old_node->find_index(k);
    if (i == -1) return std::optional(std::optional<V>());
    if (try_update(s, old_node, remove_from_node(old_node, k, i)))
      return std::optional(std::optional<V>(old_node->get_entries()[i].second));
    else return {};
  }

  static std::optional<std::optional<V>>
  try_cached_remove_at(bucket* s, const K& k) {
    cache_snapshot buffer(s);
    if (is_busy(buffer.version)) return {};
    int cnt = get_cnt(buffer.version);
    int idx = find_in_range(buffer.data(), std::min(cnt, num_cached), k);
    if (idx == -1 && cnt <= num_cached) return std::optional<V>();
    if (cnt > num_cached) return {};
    node* new_node = nullptr;
    if (cnt != 1) {
      new_node = allocate_node(cnt-1);
      KV* values = new_node->get_entries();
      copy_and_remove(values, buffer.data(), cnt, k, idx);
    }
    if (try_cached_update(s, buffer.version, new_node))
      return std::optional<V>(buffer.data()[idx].second);
    else return {};
  }

public:
  
  // *********************************************
  // The public interface
  // *********************************************

  unordered_map(size_t n) : hash_table(Table(n)) {}
  ~unordered_map() {
    auto& table = hash_table.table;
    parlay::parallel_for (0, table.size(), [&] (size_t i) {
      node* ptr = table[i].ptr.load();
      if (ptr != nullptr && ptr->cnt > num_cached)
	retire_node(table[i].ptr.load());});
  }

  static std::pair<bool, std::optional<V>> find_in_cache(bucket* s, const K& k) {
    char buffer[sizeof(KV)];
    vtype version = s->version.load();
    int cnt = get_cnt(version);
    if (cnt == 0)
      return std::pair(version, std::optional<V>());
    if (is_busy(version))
      return std::pair(-1l, std::optional<V>());
    for (int i=0; i < std::min(cnt, num_cached); i++) {
      memcpy(buffer, &s->keyval[i], sizeof(KV));
      if (version != s->version.load())
	return std::pair(-1l, std::optional<V>());
      if (((KV*) buffer)->first == k)
	return std::pair(version, std::optional<V>(((KV*) buffer)->second));
    }
    return std::pair(cnt <= num_cached ? version : -1l, std::optional<V>());
  }
    
  std::optional<V> find(const K& k) {
    bucket* s = hash_table.get_bucket(k);
    auto [ok, y] = find_in_cache(s, k);
    if (ok >= 0) return y;
    return epoch::with_epoch([&] {
      node* y = s->ptr.load();
      if (y == nullptr) return std::optional<V>();
      return y->find(k);
    });
  }

  bool insert(const K& k, const V& v) {
    bucket* s = hash_table.get_bucket(k);
    __builtin_prefetch (s);
    std::optional<V> r = epoch::with_epoch([&] {
      return epoch::try_loop([&] () -> std::optional<std::optional<V>> {
        int version = s->version.load();
	auto y = try_cached_insert_at(s, k, v);
	if (y.has_value()) return y;
	if (get_cnt(version) > num_cached || s->version.load() != version)
	  return try_insert_at(s, k, v);
	else return std::optional<std::optional<V>>();});});
    return !r.has_value();
  }

  bool remove(const K& k) {
    bucket* s = hash_table.get_bucket(k);
    __builtin_prefetch (s);
    std::optional<V> r = epoch::with_epoch([&] {
      return epoch::try_loop([&] () -> std::optional<std::optional<V>> {
        int version = s->version.load();
	auto y = try_cached_remove_at(s, k);
	if (y.has_value()) return *y;
	if (get_cnt(version) > num_cached || s->version.load() != version)
	  return try_remove_at(s, k);
	else return std::optional<std::optional<V>>();});});
    return r.has_value();
  }

  long size() {
    auto& table = hash_table.table;
    auto s = epoch::with_epoch([&] {
	       return parlay::tabulate(table.size(), [&] (size_t i) {
	         int cnt = get_cnt(table[i].version.load());
		 if (cnt <= num_cached) return cnt;
		 node* x = table[i].ptr.load();
		 if (x == nullptr) return 0;
		 else return x->cnt;});});
    return reduce(s);
  }

  parlay::sequence<KV> entries() {
    auto& table = hash_table.table;
    auto s = epoch::with_epoch([&] {
    	       return parlay::tabulate(table.size(), [&] (size_t i) {
		 cache_snapshot buffer(table + i);
		 int cnt = get_cnt(buffer.version);
		 KV* entries = buffer.data();
		 if (is_busy(buffer.version) || cnt > num_cached) {
		   node* x = table[i].ptr.load();
		   cnt = (x == nullptr) ? 0 : x->cnt;
		   entries = x->get_entries();
		 }
    		 return parlay::delayed::tabulate(cnt, [=] (long j) {
		   return entries[j];});});});
    return parlay::flatten(s);
  }

};

} // namespace parlay
#endif //PARLAYHASH_H_
