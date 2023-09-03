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
  static void copy_and_remove(Range& out, const RangeIn& entries, long cnt,
			      const K& k, const long idx) {
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
    const int cnt;
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

  static constexpr int mask_bits = 4;
  static constexpr unsigned long mask = (1ul << mask_bits)-1ul;
  static constexpr int num_cached = 3;

  static unsigned long next_version(unsigned long version) {
    return ((version >> mask_bits) + 1ul) << mask_bits;
  }

  static unsigned long get_cnt(unsigned long version) {
    return (version & mask);
  }

  struct alignas(64) bucket {
    std::atomic<node*> ptr;
    std::atomic<unsigned long> version;
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

  static void load_cache(bucket* s, node* new_node, unsigned int version) {
    if (new_node != nullptr) {
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

  static int get_size(bucket* s) {
    int cnt = get_cnt(s->version.load());
    if (cnt > num_cached) {
      node* old_node = s->ptr.load();
      if (old_node == nullptr) return 0;
      else return old_node->cnt;
    }
    return cnt;
  }
    
  static std::optional<std::optional<V>>
  try_insert_at(bucket* s, const K& k, const V& v) {
    //std::cout << k << std::endl;
    int cnt = get_size(s);
    bool is_cached_old = (cnt <= num_cached);
    bool is_cached_new = (cnt + 1 <= num_cached);
    node* new_node = allocate_node(cnt + 1);
    std::optional<V> rval{};
    node* old_node = s->ptr.load();
    if (get_locks().try_lock((long) s, [&] {
	  if (get_size(s) != cnt || old_node != s->ptr.load()) return false;
 	  auto version = next_version(s->version.load());
	  KV* new_vals = new_node->get_entries();
	  if (old_node != nullptr) {
	    //KV* old_vals = is_cached_old ? s->keyval : old_node->get_entries();
	    KV* old_vals = old_node->get_entries();
	    int loc = find_in_range(old_vals, cnt, k);
	    //std::cout << "x: " << loc << ", " << k << std::endl;
	    // for (int i=0; i < cnt; i++)
	    //   std::cout << old_vals[i].first << ", ";
	    // std::cout << std::endl;
	    if (loc != -1) {
	      rval = std::optional(old_vals[loc].second);
	      return true;
	    }
	    copy_and_insert(new_vals, old_vals, cnt, k, v);
	  } else copy_and_insert(new_vals, (KV*) nullptr, 0, k, v);
	  s->ptr = new_node;
	  s->version = version + 5;
	  load_cache(s, new_node, version);
	  return true;}))
      if (rval.has_value()) {
	//std::cout << "here" << std::endl;
	retire_node(new_node);
	return std::optional(rval);
      } else {
	if (is_cached_new) retire_node(new_node);
	if (!is_cached_old)
	  retire_node(old_node);
	return std::optional(rval);
      }
    retire_node(new_node);
    return {};
  }

  static std::optional<std::optional<V>>
  try_remove_at(bucket* s, const K& k) {
    int cnt = get_size(s);
    if (cnt == 0) return std::optional(std::optional<V>());
    bool is_cached_old = (cnt <= num_cached);
    bool is_cached_new = (cnt - 1 <= num_cached);
    node* new_node = allocate_node(cnt - 1);
    std::optional<V> rval;
    node* old_node = s->ptr.load();
    if (get_locks().try_lock((long) s, [&] {
	  if (get_size(s) != cnt || old_node != s->ptr.load()) return false;
	  auto version = next_version(s->version.load());
	  //KV* old_vals = is_cached_old ? s->keyval : old_node->get_entries();
	  KV* old_vals = old_node->get_entries();
	  int loc = find_in_range(old_vals, cnt, k);
	  if (loc == -1) return true;
	  else rval = std::optional(old_vals[loc].second);
	  if (new_node != nullptr) {
	    KV* new_vals = new_node->get_entries();
	    copy_and_remove(new_vals, old_vals, cnt, k, loc);
	  }
	  s->ptr = new_node;
	  s->version = version + 5;
	  load_cache(s, new_node, version);
	  return true;}))
      if (!rval.has_value()) {
	retire_node(new_node);
	return std::optional(rval);
      } else {
	if (is_cached_new) retire_node(new_node);
	if (!is_cached_old)
	  retire_node(old_node);
	return std::optional(rval);
      }
    retire_node(new_node);
    return {};
  }

  // static std::optional<std::optional<V>> try_remove_at(bucket* s, const K& k) {
  //     node* old_node = s->ptr.load();
  //     int i = (old_node == nullptr) ? -1 : old_node->find_index(k);
  //     if (i == -1) return std::optional(std::optional<V>());
  //     if (try_update(s, old_node, remove_from_node(old_node, k, i)))
  // 	return std::optional(std::optional<V>(old_node->get_entries()[i].second));
  //     else return {};
  // }

public:
  // *********************************************
  // The public interface
  // *********************************************

  unordered_map(size_t n) : hash_table(Table(n)) {}
  ~unordered_map() {
    auto& table = hash_table.table;
    parlay::parallel_for (0, table.size(), [&] (size_t i) {
      retire_node(table[i].ptr.load());});
  }

  std::pair<bool, std::optional<V>> find_in_cache(bucket* s, int cnt, unsigned int version, const K& k) {
    char buffer[sizeof(KV)];
    for (int i=0; i < std::min(cnt, num_cached); i++) {
      memcpy(buffer, &s->keyval[i], sizeof(KV));
      if (version != s->version.load())
	return std::make_pair(false, std::optional<V>());
      if (((KV*) buffer)->first == k)
	return std::make_pair(true, std::optional<V>(((KV*) buffer)->second));
    }
    return std::make_pair(cnt <= num_cached, std::optional<V>());
  }
    
  std::optional<V> find(const K& k) {
    bucket* s = hash_table.get_bucket(k);
    node* x = s->ptr.load();
    long version = s->version.load();
    int cnt = version & mask;
    if (cnt == 0) return std::optional<V>();
    if (cnt != 5) {
      auto [ok, x] = find_in_cache(s, cnt, version, k);
      if (ok) return x;
    }
    return epoch::with_epoch([&] {
      if (cnt <= num_cached) {
        auto [ok, x] = find_in_cache(s, cnt, version, k);
	if (ok) return x;
      }
      node* x = s->ptr.load();
      if (x == nullptr) return std::optional<V>();
      return x->find(k);
    });
  }

  bool insert(const K& k, const V& v) {
    bucket* s = hash_table.get_bucket(k);
    long version = s->version.load();
    int cnt = version & mask;
    if (cnt != 5 && cnt != 0) {
      auto [ok, x] = find_in_cache(s, cnt, version, k);
      if (ok && x.has_value()) {
	return false;
      }
    }
    //std::cout << "inserting " << k << std::endl;
    return epoch::with_epoch([&] {
      auto y = epoch::try_loop([&] {return try_insert_at(s, k, v);});
      //std::cout << "has value: " << y.has_value() << std::endl;
      return !y.has_value();});
  }

  // template <typename F>
  // bool upsert(const K& k, const F& f) {
  //   bucket* s = hash_table.get_bucket(k);
  //   __builtin_prefetch (s);
  //   return epoch::with_epoch([&] {
  //     return epoch::try_loop([&] {return try_upsert_at(s, k, f);});});
  // }

  bool remove(const K& k) {
    bucket* s = hash_table.get_bucket(k);
    long version = s->version.load();
    int cnt = version & mask;
    if (cnt == 0) return false;
    if (cnt <= num_cached) {
      auto [ok, x] = find_in_cache(s, cnt, version, k);
      if (ok && !x.has_value())	return false;
    }
    return epoch::with_epoch([&] {
      auto y = epoch::try_loop([&] {return try_remove_at(s, k);});
      return y.has_value();});
  }

  long size() {
    auto& table = hash_table.table;
    auto s = epoch::with_epoch([&] {
	       return parlay::tabulate(table.size(), [&] (size_t i) {
		 node* x = table[i].ptr.load();
		 if (x == nullptr) return 0;
		 else return x->cnt;});});
    return reduce(s);
  }

  parlay::sequence<KV> entries() {
    auto& table = hash_table.table;
    auto s = epoch::with_epoch([&] {
    	       return parlay::tabulate(table.size(), [&] (size_t i) {
    	         node* x = table[i].ptr.load();
		 long cnt = (x == nullptr) ? 0 : x->cnt;
    		 return parlay::delayed::tabulate(cnt, [=] (long j) {
		   return x->get_entries()[j];});});});
    return parlay::flatten(s);
  }

};

} // namespace parlay
#endif //PARLAYHASH_H_

