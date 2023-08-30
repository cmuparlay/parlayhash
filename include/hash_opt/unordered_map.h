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

  using bucket = std::atomic<node*>;
  struct alignas(64) entry {
    bucket ptr;
    std::atomic<unsigned long> cnt;
    KV keyval[3];
    entry() : ptr(nullptr), cnt(0) {}
  };

  struct Table {
    parlay::sequence<entry> table;
    size_t size;
    bucket* get_bucket(const K& k) {
      size_t idx = Hash{}(k)  & (size-1u);
      return &(table[idx].ptr);
    }
    entry* get_entry(const K& k) {
      size_t idx = Hash{}(k)  & (size-1u);
      return &(table[idx]);
    }
    Table(size_t n) {
      int bits = parlay::log2_up(n);
      size = 1ul << bits;
      table = parlay::sequence<entry>(size);
    }
  };

  Table hash_table;

  // *********************************************
  // The internal update functions (insert, upsert and remove)
  // *********************************************


  // try to install a new node in bucket s
  static bool try_update(entry* s, node* old_node, node* new_node) {
#ifndef USE_LOCKS
    if (s->ptr.load() == old_node &&
	s->ptr.compare_exchange_strong(old_node, new_node)) {
#else  // use try_lock
    if (get_locks().try_lock((long) s, [=] {
	    if (s->ptr.load() != old_node) return false;
	    s->ptr = new_node;
	    return true;})) {
#endif
      if (new_node != nullptr && new_node->cnt < 4) {
	s->keyval[0] = new_node->entries[0];
	if (new_node->cnt == 1)
	  s->cnt = ((s->cnt.load()) & ~3ul) + 5;
	else {
	  s->keyval[1] = new_node->entries[1];
	  if (new_node->cnt == 2)
	    s->cnt = ((s->cnt.load()) & ~3ul) + 6;
	  else {
	    s->keyval[2] = new_node->entries[2];
	    s->cnt = ((s->cnt.load()) & ~3ul) + 7;
	    }
	}
      } else s->cnt = ((s->cnt.load()) & ~3ul) + 4;
      retire_node(old_node);
      return true;
    } 
    destruct_node(new_node);
    return false;
  }

  static std::optional<std::optional<V>>
  try_insert_at(entry* s, const K& k, const V& v) {
    node* old_node = s->ptr.load();
    auto x = (old_node == nullptr) ? std::nullopt : old_node->find(k);
    if (x.has_value()) return std::optional(x);
    if (try_update(s, old_node, insert_to_node(old_node, k, v)))
      return std::optional(std::optional<V>());
    else return {};
  }

  template <typename F>
  static std::optional<bool> try_upsert_at(entry* s, const K& k, F& f) {
    node* old_node = s->load();
    long idx;
    bool found = old_node != nullptr && (idx = old_node->find_index(k)) != -1;
    if (!found)
      if (try_update(s, old_node, insert_to_node(old_node, k, f(std::optional<V>()))))
	return true;
      else return {};
    else
#ifndef USE_LOCKS
      if (try_update(s, old_node, update_node(old_node, k, f, idx))) return false;
      else return {};
#else  // use try_lock
    if (get_locks().try_lock((long) s, [=] {
        if (s->load() != old_node) return false;
	*s = update_node(old_node, k, f, idx); // f applied within lock
	return true;})) {
      retire_node(old_node);
      return false;
    } else return {};
#endif
  }

  static std::optional<std::optional<V>> try_remove_at(entry* s, const K& k) {
      node* old_node = s->ptr.load();
      int i = (old_node == nullptr) ? -1 : old_node->find_index(k);
      if (i == -1) return std::optional(std::optional<V>());
      if (try_update(s, old_node, remove_from_node(old_node, k, i)))
	return std::optional(std::optional<V>(old_node->get_entries()[i].second));
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
      retire_node(table[i].ptr.load());});
  }
  
  std::optional<V> find(const K& k) {
    entry* s = hash_table.get_entry(k);
    long cnt = s->cnt.load();
    node* x = s->ptr.load();
    if (x == nullptr) return std::optional<V>();
    if ((cnt & 3ul) && (s->cnt.load() == cnt)) {
      if (s->keyval[0].first == k)
	return std::optional<V>(s->keyval[0].second);
      if ((cnt & 2ul) && s->keyval[1].first == k)
	return std::optional<V>(s->keyval[1].second);
      if ((cnt & 3ul) == 3 && s->keyval[2].first == k) 
	return std::optional<V>(s->keyval[2].second);
      return std::optional<V>();
    }
    return epoch::with_epoch([&] {
      node* x = s->ptr.load();
      if (x == nullptr) return std::optional<V>();
      return x->find(k);
      });
  }

  bool insert(const K& k, const V& v) {
    entry* s = hash_table.get_entry(k);
    __builtin_prefetch (s);
    return epoch::with_epoch([&] {
      auto y = epoch::try_loop([&] {return try_insert_at(s, k, v);});
      return !y.has_value();});
  }

  template <typename F>
  bool upsert(const K& k, const F& f) {
    entry* s = hash_table.get_entry(k);
    __builtin_prefetch (s);
    return epoch::with_epoch([&] {
      return epoch::try_loop([&] {return try_upsert_at(s, k, f);});});
  }

  bool remove(const K& k) {
    entry* s = hash_table.get_entry(k);
    __builtin_prefetch (s);
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
