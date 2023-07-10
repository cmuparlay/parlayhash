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

#include <atomic>
#include <optional>
#include "epoch.h"
#include "lock.h"
#include <parlay/primitives.h>
#define USE_LOCKS 1

template <typename K,
	  typename V,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_map {
private:
  struct KV {K key; V value;};

  template <typename Range>
  static int find_in_range(const Range& entries, long cnt, const K& k) {
    for (int i=0; i < cnt; i++)
      if (KeyEqual{}(entries[i].key, k)) return i;
    return -1;
  }

  // The following three functions copy a range and
  // insert/update/remove the specified key.  No ordering is assumed
  // within the range.  Insert assumes k does not appear, while
  // update/remove assume it does appear.
  template <typename Range, typename RangeIn>
  static void copy_and_insert(Range& out, const RangeIn& entries, long cnt, const K& k, const V& v) {
    for (int i=0; i < cnt; i++) out[i] = entries[i];
    out[cnt] = KV{k,v};
  }

  template <typename Range, typename RangeIn, typename F>
  static void copy_and_update(Range& out, const RangeIn& entries, long cnt, const K& k, const F& f) {
    int i = 0;
    while (!KeyEqual{}(k, entries[i].key) && i < cnt) {
      assert(i < cnt);
      out[i] = entries[i];
      i++;
    }
    out[i].key = entries[i].key;
    out[i].value = f(entries[i].value);
    i++;
    while (i < cnt) {
      out[i] = entries[i];
      i++;
    }
  }

  template <typename Range, typename RangeIn>
  static void copy_and_remove(Range& out, const RangeIn& entries, long cnt, const K& k) {
    int i = 0;
    while (!KeyEqual{}(k, entries[i].key)) {
      assert(i < cnt);
      out[i] = entries[i];
      i++;
    }
    while (i < cnt-1) {
      out[i] = entries[i+1];
      i++;
    }
  }

  // Each bucket points to a Node of some Size, or to a BigNode (defined below)
  // A node contains an array of up to Size entries (actual # of entries given by cnt)
  // Sizes are 1, 3, 7, 31
  template <int Size>
  struct Node {
    using node = Node<0>;
    int cnt;
    KV entries[Size];

    // return index of key in entries, or -1 if not found
    int find_index(const K& k) {
      if (cnt <= 31) return find_in_range(entries, cnt, k);
      else return find_in_range(((BigNode*) this)->entries, cnt, k);
    }

    // return optional value found in entries given a key
    inline std::optional<V> find(const K& k) {
      if (cnt <= 31) { // regular node
	int i = find_index(k);
	if (i == -1) return {};
	else return entries[i].value;
      } else { // big node
	abort();
	//return {};
	// int i = find_in_range(((BigNode*) this)->entries, cnt, k);
	// //int i = find_index(k);
	// if (i == -1) return {};
	// else return ((BigNode*) this)->entries[i].value;
	// //else return entries[i].value;
      }
    }

    // copy and insert
    Node(node* old, const K& k, const V& v) {
      cnt = (old == nullptr) ? 1 : old->cnt + 1;
      copy_and_insert(entries, old->entries, cnt-1, k, v);
    }

    // copy and update
    template <typename F>
    Node(node* old, const K& k, const F& f) : cnt(old->cnt) {
      assert(old != nullptr);
      copy_and_update(entries, old->entries, cnt, k, f);
    }

    // copy and remove
    Node(node* old, const K& k) : cnt(old->cnt - 1) {
      if (cnt == 31) copy_and_remove(entries, ((BigNode*) old)->entries, cnt+1, k);
      else 
	copy_and_remove(entries, old->entries, cnt+1, k);
    }
  };
  using node = Node<0>;

  // If a node overflows (cnt > 31), then it becomes a big node and its content
  // is stored indirectly in a parlay sequence.
  struct BigNode {
    using entries_type = parlay::sequence<KV>;
    //using entries_type = std::vector<KV>;
    int cnt;
    entries_type entries;

    BigNode(node* old, const K& k, const V& v) : cnt(old->cnt + 1) {
      entries = entries_type(cnt);
      if (old->cnt == 31) copy_and_insert(entries, old->entries, old->cnt, k, v);
      else copy_and_insert(entries, ((BigNode*) old)->entries, old->cnt, k, v);
    }

    template <typename F>
    BigNode(node* old, const K& k, const F& f) : cnt(old->cnt) {
      entries = entries_type(cnt);
      copy_and_update(entries, ((BigNode*) old)->entries, cnt, k, f);
    }

    BigNode(node* old, const K& k) : cnt(old->cnt - 1) {
      entries = entries_type(cnt);
      copy_and_remove(entries, ((BigNode*) old)->entries, cnt+1, k);
    }
  };

  // a
  //memory pool for each node size
  using Pool1 = flck::memory_pool<Node<1>>;
  using Pool3 = flck::memory_pool<Node<3>>;
  using Pool7 = flck::memory_pool<Node<7>>;
  using Pool31 = flck::memory_pool<Node<31>>;
  using PoolBig = flck::memory_pool<BigNode>;

  // the following functions branch to construct the right sized node
  static node* insert_to_node(node* old, const K& k, const V& v) {
    if (old == nullptr) return (node*) Pool1::New(old, k, v);
    if (old->cnt < 3) return (node*) Pool3::New(old, k, v);
    else if (old->cnt < 7) return (node*) Pool7::New(old, k, v);
    else if (old->cnt < 31) return (node*) Pool31::New(old, k, v);
    else return (node*) PoolBig::New(old, k, v);
  }

  template <typename F>
  static node* update_node(node* old, const K& k, const F& f) {
    assert(node != nullptr);
    if (old->cnt == 1) return (node*) Pool1::New(old, k, f);
    if (old->cnt <= 3) return (node*) Pool3::New(old, k, f);
    else if (old->cnt <= 7) return (node*) Pool7::New(old, k, f);
    else if (old->cnt <= 31) return (node*) Pool31::New(old, k, f);
    else return (node*) PoolBig::New(old, k, f);
  }

  static node* remove_from_node(node* old, const K& k) {
    assert(node != nullptr);
    if (old->cnt == 1) return (node*) nullptr;
    if (old->cnt == 2) return (node*) Pool1::New(old, k);
    else if (old->cnt <= 4) return (node*) Pool3::New(old, k);
    else if (old->cnt <= 8) return (node*) Pool7::New(old, k);
    else if (old->cnt <= 32) return (node*) Pool31::New(old, k);
    else return (node*) PoolBig::New(old, k);
  }

  static void retire_node(node* old) {
    if (old == nullptr);
    else if (old->cnt == 1) Pool1::Retire((Node<1>*) old);
    else if (old->cnt <= 3) Pool3::Retire((Node<3>*) old);
    else if (old->cnt <= 7) Pool7::Retire((Node<7>*) old);
    else if (old->cnt <= 31) Pool31::Retire((Node<31>*) old);
    else PoolBig::Retire((BigNode*) old);
  }

  static void destruct_node(node* old) {
    if (old == nullptr);
    else if (old->cnt == 1) Pool1::Delete((Node<1>*) old);
    else if (old->cnt <= 3) Pool3::Delete((Node<3>*) old);
    else if (old->cnt <= 7) Pool7::Delete((Node<7>*) old);
    else if (old->cnt <= 31) Pool31::Delete((Node<31>*) old);
    else PoolBig::Delete((BigNode*) old);
  }

  // *********************************************
  // The bucket and table structures
  // *********************************************

  using bucket = std::atomic<node*>;

  struct Table {
    parlay::sequence<bucket> table;
    size_t size;
    bucket* get_bucket(const K& k) {
      size_t idx = Hash{}(k)  & (size-1u);
      return &table[idx];
    }
    Table(size_t n) {
      int bits = 1 + parlay::log2_up(n);
      size = 1ul << bits;
      table = parlay::sequence<bucket>(size);
    }
  };

  Table hash_table;

  // *********************************************
  // The internal update functions (insert, upsert and remove)
  // *********************************************


  // try to install a new node in bucket s
  static std::optional<bool> try_update(bucket* s, node* old_node, node* new_node, bool ret_val) {
#ifndef USE_LOCKS
    if (s->load() == old_node &&
	s->compare_exchange_strong(old_node, new_node)) {
#else  // use try_lock
    if (locks.try_lock((long) s, [=] {
	    if (s->load() != old_node) return false;
	    *s = new_node;
	    return true;})) {
#endif
      retire_node(old_node);
      return ret_val;
    } 
    destruct_node(new_node);
    return {};
  }

  static std::optional<bool> try_insert_at(bucket* s, const K& k, const V& v) {
    node* old_node = s->load();
    if (old_node != nullptr && old_node->find_index(k) != -1) return false;
    return try_update(s, old_node, insert_to_node(old_node, k, v), true);
  }

  template <typename F>
  static std::optional<bool> try_upsert_at(bucket* s, const K& k, F& f) {
    node* old_node = s->load();
    bool found = old_node != nullptr && old_node->find_index(k) != -1;
    if (!found)
      return try_update(s, old_node, insert_to_node(old_node, k, f(std::optional<V>())), true);
    else
#ifndef USE_LOCKS
      return try_update(s, old_node, update_node(old_node, k, f), false);
#else  // use try_lock
    if (locks.try_lock((long) s, [=] {
        if (s->load() != old_node) return false;
	*s = update_node(old_node, k, f); // f applied within lock
	return true;})) {
      retire_node(old_node);
      return false;
    } else return {};
#endif
  }

  static std::optional<bool> try_remove_at(bucket* s, const K& k) {
      node* old_node = s->load();
      if (old_node == nullptr || old_node->find_index(k) == -1) return false;
      return try_update(s, old_node, remove_from_node(old_node, k), true);
  }

public:
  // *********************************************
  // The public interface
  // *********************************************

  unordered_map(size_t n) : hash_table(Table(n)) {}
  ~unordered_map() {
    auto& table = hash_table.table;
    parlay::parallel_for (0, table.size(), [&] (size_t i) {
      retire_node(table[i].load());});
  }
  
  std::optional<V> find(const K& k) {
    bucket* s = hash_table.get_bucket(k);
    __builtin_prefetch (s);
    return flck::with_epoch([&] {
      node* x = s->load();
      if (x == nullptr) return std::optional<V>();
      //if (KeyEqual{}(x->entries[0].key, k))
      //  return std::optional<V>(x->entries[0].value);
      return std::optional<V>(x->find(k));
    });
  }

  bool insert(const K& k, const V& v) {
    bucket* s = hash_table.get_bucket(k);
    __builtin_prefetch (s);
    return flck::with_epoch([&] {
      return flck::try_loop([&] {return try_insert_at(s, k, v);});});
  }

  template <typename F>
  bool upsert(const K& k, const F& f) {
    bucket* s = hash_table.get_bucket(k);
    __builtin_prefetch (s);
    return flck::with_epoch([&] {
      return flck::try_loop([&] {return try_upsert_at(s, k, f);});});
  }

  bool remove(const K& k) {
    bucket* s = hash_table.get_bucket(k);
    __builtin_prefetch (s);
    return flck::with_epoch([&] {
      return flck::try_loop([&] {return try_remove_at(s, k);});});
  }

  long size() {
    auto& table = hash_table.table;
    auto s = parlay::tabulate(table.size(), [&] (size_t i) {
	      node* x = table[i].load();
	      if (x == nullptr) return 0;
	      else return x->cnt;});
    return parlay::reduce(s);
  }
};