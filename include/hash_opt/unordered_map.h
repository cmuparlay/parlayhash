// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 
// A concurrent unordered_map using a hash table.  Updates use locks,
// but finds are lock free.
// On a key type K and value type V it supports:
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
//   ** NEED TO ADD
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
// The type for keys and values must be copyable, and might be copied
// by the hash_table even when not being updated (e.g. when another
// key in the same bucket is being updated). 

#ifndef PARLAYHASH_H_
#define PARLAYHASH_H_

#define MEM_STATS 1
//#define WAIT_FREE_FINDS 1

#include <atomic>
#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include <parlay/delayed.h>
#include "epoch.h"
#include "lock.h"

namespace parlay {
  
template <typename K,
	  typename V,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_map {
private:
  using KV = std::pair<K,V>;
#ifdef WAIT_FREE_FINDS
    static constexpr bool default_backup = true;
#else
    static constexpr bool default_backup = false;
#endif

  template <typename Range>
  static int find_in_range(const Range& entries, long cnt, const K& k) {
    for (int i=0; i < cnt; i++)
      if (KeyEqual{}(entries[i].first, k)) return i;
    return -1;
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

    Node(int cnt) : cnt(cnt) {}
  };
  using node = Node<0>;

  // If a node overflows (cnt > 31), then it becomes a big node and its content
  // is stored indirectly in an std::vector.
  struct BigNode {
    using entries_type = parlay::sequence<KV>;
    int cnt;
    entries_type entries;

    BigNode(int cnt) : cnt(cnt) {
      entries = parlay::tabulate(cnt, [] (long i) {return KV{};}, cnt);
    }
  };

  static void retire_node(node* old) {
    if (old == nullptr);
    else if (old->cnt == 1) epoch::memory_pool<Node<1>>::Retire((Node<1>*) old);
    else if (old->cnt <= 3) epoch::memory_pool<Node<3>>::Retire((Node<3>*) old);
    else if (old->cnt <= 7) epoch::memory_pool<Node<7>>::Retire((Node<7>*) old);
    else if (old->cnt <= 31) epoch::memory_pool<Node<31>>::Retire((Node<31>*) old);
    else epoch::memory_pool<BigNode>::Retire((BigNode*) old);
  }

  static node* allocate_node(int cnt) {
    if (cnt == 0) return nullptr;
    else if (cnt == 1) return (node*) epoch::memory_pool<Node<1>>::New(cnt);
    else if (cnt <= 3) return (node*) epoch::memory_pool<Node<3>>::New(cnt);
    else if (cnt <= 7) return (node*)epoch::memory_pool<Node<7>>::New(cnt);
    else if (cnt <= 31) return (node*) epoch::memory_pool<Node<31>>::New(cnt);
    else return (node*) epoch::memory_pool<BigNode>::New(cnt);
  }

  // *********************************************
  // The bucket and table structures
  // *********************************************

  using vtype = long;
  
  static constexpr int mask_bits = 8;
  static constexpr vtype mask = (1l << mask_bits)-1l;
  static constexpr int num_cached = 3;
  static constexpr vtype busy_version = -1;
  static constexpr long locked_ptr = -1;

  static vtype next_version(vtype version) {
    return ((version >> mask_bits) + 1l) << mask_bits;
  }

  static int get_cnt(vtype version) {
    return (version & mask);
  }

  // the version is marked as busy when the cache is updated
  static bool is_busy(vtype v) {return v == busy_version;}

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
      size_t idx = Hash{}(k) & (size-1u);
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
  // The internal update functions (insert and remove)
  // *********************************************

  // read a snapshot from the cache, and put in buffer
  // the snapshot is associated with a version
  struct cache_snapshot {
    KV* data() {return ok ? (KV*) buffer : nullptr;}
    cache_snapshot(bucket* s, vtype version) : ok(true) {
      assert(!is_busy(version));
      int cnt = std::min(get_cnt(version), num_cached);
      memcpy(buffer, s->keyval, cnt*sizeof(KV));
      if (s->version.load() != version) ok = false;
    }
  private:
    char buffer[sizeof(KV)*num_cached];
    bool ok;
  };

  // insert into a bucket from an old node
  static std::optional<std::optional<V>>
  try_insert_at(bucket* s, vtype version, const K& k, const V& v) {
    node* old_node = s->ptr.load();
    if (s->version.load() != version) return {};
    int cnt = old_node->cnt;
    auto x = old_node->find(k);
    if (x.has_value()) return std::optional(x);
    KV* old_values = old_node->get_entries();
    node* new_node = allocate_node(cnt+1);
    KV* values = new_node->get_entries();
    for (int i=0; i < cnt; i++) values[i] = old_values[i];
    values[cnt] = KV{k,v};
    if (get_locks().try_lock((long) s, [&] {
        if (s->version.load() != version) return false;
	vtype nxt_version = next_version(version);
	s->version = busy_version;
	s->ptr = new_node;
	s->version = nxt_version + num_cached + 1;
	return true;})) {
      retire_node(old_node);
      return std::optional(std::optional<V>());
    }
    retire_node(new_node);
    return {};
  }
  
  // insert into a bucket that is fully cached
  static std::optional<std::optional<V>>
  try_cached_insert_at(bucket* s, vtype version, const K& k, const V& v, bool backup) {
    cache_snapshot buffer(s, version);
    KV* data = buffer.data();
    if (data == nullptr) return {};
    int cnt = get_cnt(version);
    int idx = find_in_range(data, cnt, k);
    if (idx != -1) return std::optional(data[idx].second);
    node* old_node;
    if (backup) {
      old_node = allocate_node(cnt);
      if (old_node != nullptr)
	for (int i=0; i < cnt; i++)
	  old_node->get_entries()[i] = data[i];
    }
    if (get_locks().try_lock((long) s, [&] {
        if (s->version.load() != version) return false;
	if (backup) s->ptr = old_node;
	else s->ptr = (node*) locked_ptr;
	vtype nxt_version = next_version(version);
	s->version = busy_version;
	if (cnt < num_cached) {
	  s->keyval[cnt] = KV{k,v};
	  s->version = nxt_version + cnt + 1;
	} else {
	  node* new_node = allocate_node(cnt + 1);
	  for (int i=0; i < cnt; i++)
	    new_node->get_entries()[i] = data[i];
	  new_node->get_entries()[cnt] = KV{k,v};
	  s->ptr = new_node;
	  s->version = nxt_version + num_cached + 1;
	}
	return true;})) {
      if (backup) retire_node(old_node);
      return std::optional(std::optional<V>());
    }
    if (backup) retire_node(old_node);
    return {};
  }

  static std::optional<std::optional<V>>
  try_remove_at(bucket* s, vtype version, const K& k) {
    node* old_node = s->ptr.load();
    if (s->version.load() != version) return {};
    int idx = old_node->find_index(k);
    if (idx == -1) return std::optional(std::optional<V>());
    KV* old_values = old_node->get_entries();
    int new_cnt = old_node->cnt - 1;
    node* new_node = allocate_node(new_cnt);
    KV* new_values = new_node->get_entries();
    for (int i = 0; i < idx; i++) new_values[i] = old_values[i];
    for (int i = idx; i < new_cnt; i++) new_values[i] = old_values[i+1];
    if (get_locks().try_lock((long) s, [&] {
        if (s->ptr.load() != old_node) return false;
	vtype nxt_version = next_version(s->version.load());
	s->version = busy_version;
	if (idx < num_cached && idx < new_cnt)
	  s->keyval[idx] = new_values[idx];
	s->ptr = new_node;
	s->version = nxt_version + std::min(new_cnt, num_cached +1);
	return true;})) {
      retire_node(old_node);
      if (new_cnt == num_cached) retire_node(new_node);
      return std::optional(std::optional<V>(old_values[idx].second));
    } else {
      retire_node(new_node);
      return {};
    }
  }

  static std::optional<std::optional<V>>
  try_cached_remove_at(bucket* s, vtype version, const K& k, bool backup) {
    cache_snapshot buffer(s, version);
    KV* data = buffer.data();
    if (data == nullptr) return {};
    int cnt = get_cnt(version);
    int idx = find_in_range(data, cnt, k);
    if (idx == -1) return std::optional<V>();
    V r = data[idx].second;
    node* old_node = nullptr;
    if (backup) {
      old_node = allocate_node(cnt);
      for (int i=0; i < cnt; i++)
	old_node->get_entries()[i] = data[i];
    }
    if (get_locks().try_lock((long) s, [&] {
        if (s->version.load() != version) return false;
	if (backup) s->ptr = old_node;
	else s->ptr = (node*) locked_ptr;
	vtype nxt_version = next_version(version);
	if (backup) s->version = busy_version;
	if (cnt - 1 < idx)
	  s->keyval[idx] = std::move(s->keyval[cnt - 1]);
	s->version = nxt_version + cnt - 1;
	return true;})) {
      if (backup) retire_node(old_node);
      return std::optional<V>(r);
    }
    if (backup) retire_node(old_node);
    return {};
  }

    static std::pair<bool, std::optional<V>> find_in_cache(bucket* s, const K& k) {
    char buffer[sizeof(KV)];
    vtype version = s->version.load();
    int cnt = get_cnt(version);
    if (cnt == 0)
      return std::pair(true, std::optional<V>());
    if (is_busy(version))
      return std::pair(false, std::optional<V>());
    for (int i=0; i < std::min(cnt, num_cached); i++) {
      memcpy(buffer, &s->keyval[i], sizeof(KV));
      if (version != s->version.load())
	return std::pair(false, std::optional<V>());
      if (((KV*) buffer)->first == k)
	return std::pair(true, std::optional<V>(((KV*) buffer)->second));
    }
    return std::pair(cnt <= num_cached, std::optional<V>());
  }

public:
  
  // *********************************************
  // The public interface
  // *********************************************

  unordered_map(size_t n) : hash_table(Table(n)) {}
  ~unordered_map() {
    auto& table = hash_table.table;
    parlay::parallel_for (0, table.size(), [&] (size_t i) {
      if (get_cnt(table[i].version.load()) > num_cached) {
	node* ptr = table[i].ptr.load();
	if (ptr != nullptr && ptr->cnt > num_cached) 
	  retire_node(table[i].ptr.load());}});
  }

  std::optional<V> find(const K& k) {
    bucket* s = hash_table.get_bucket(k);
    auto [ok, y] = find_in_cache(s, k);
    if (ok) return y;
    return epoch::with_epoch([&] {
      while (true) {
	if (get_cnt(s->version.load()) <= num_cached) {	       
	  auto [ok, y] = find_in_cache(s, k);
	  if (ok) return y;}
	node* y = s->ptr.load();
	if (y == nullptr) return std::optional<V>();
	if (y != (node*) locked_ptr) return y->find(k);
	std::optional<V> r;
	if (get_locks().try_lock((long) s, [&] {
	    vtype version = s->version.load();
	    int cnt = get_cnt(version);
	    if (cnt <= num_cached) {
	      int idx = find_in_range(s->keyval, cnt, k);
	      if (idx != -1) r = std::optional<V>(s->keyval[idx].second);
	      // if (s->ptr.load() == (node*) locked_ptr) {
	      // 	node* old_node = allocate_node(cnt);
	      // 	for (int i=0; i < cnt; i++)
	      // 	  old_node->get_entries()[i] = s->keyval[i];
	      // 	s->ptr = old_node;
	      // 	retire_node(old_node);
	      // }
	    } else r = (s->ptr.load())->find(k);
	    return true;}))
	  return r;
      }}); // end while and with_epoch
  }

  bool insert(const K& k, const V& v, bool backup = default_backup) {
    bucket* s = hash_table.get_bucket(k);
    __builtin_prefetch (s);
    std::optional<V> r = epoch::with_epoch([&] {
      return epoch::try_loop([&] () -> std::optional<std::optional<V>> {
	auto [ok, x] = find_in_cache(s, k);
	if (ok && x.has_value()) return x;
        int version = s->version.load();
	if (is_busy(version)) {
	  node* y = s->ptr.load();
	  if (y != nullptr && y != (node*) locked_ptr) {
	    auto r =  y->find(k);
	    if (r.has_value()) return r;
	  }
	  return {};
	} else if (get_cnt(version) <= num_cached)
	  return try_cached_insert_at(s, version, k, v, backup);
	else return try_insert_at(s, version, k, v);
	});});
    return !r.has_value();
  }

  bool remove(const K& k, bool backup = default_backup) {
    bucket* s = hash_table.get_bucket(k);
    __builtin_prefetch (s);
    std::optional<V> r = epoch::with_epoch([&] {
      auto [ok, x] = find_in_cache(s, k);
      if (ok && !x.has_value()) return x;
      return epoch::try_loop([&] () -> std::optional<std::optional<V>> {
        int version = s->version.load();
	if (is_busy(version)) {
	  node* y = s->ptr.load();
	  if (y != nullptr && y != (node*) locked_ptr) {
	    auto r =  y->find(k);
	    if (!r.has_value()) return r;
	  }
	  return {};
	} else if (get_cnt(version) <= num_cached)
	  return try_cached_remove_at(s, version, k, backup);
	else return try_remove_at(s, version, k);});});
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
	         vtype version = table[i].version.load();
		 cache_snapshot buffer(table.begin() + i, version);
		 int cnt = get_cnt(version);
		 KV* entries = buffer.data();
		 if (entries == nullptr || cnt > num_cached) {
		   node* x = table[i].ptr.load();
		   cnt = (x == nullptr) ? 0 : x->cnt;
		   entries = x->get_entries();
		 }
    		 return parlay::delayed::tabulate(cnt, [=] (long j) {
		   return entries[j];});});});
    return parlay::flatten(s);
  }

  static void stats() {
    epoch::memory_pool<Node<1>>::stats();
    epoch::memory_pool<Node<3>>::stats();
    epoch::memory_pool<Node<7>>::stats();
    epoch::memory_pool<Node<31>>::stats();
  }


  static void clear() {
    epoch::memory_pool<Node<1>>::clear();
    epoch::memory_pool<Node<3>>::clear();
    epoch::memory_pool<Node<7>>::clear();
    epoch::memory_pool<Node<31>>::clear();
  }
};

} // namespace parlay
#endif //PARLAYHASH_H_
