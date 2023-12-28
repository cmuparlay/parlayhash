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

#ifndef PARLAYMAP_H_
#define PARLAYMAP_H_

#include <optional>
#include <functional>
#include "../parlay/sequence.h"

#include "parlay_hash.h"

namespace parlay {
  
template <typename K,
	  typename V,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct parlay_unordered_map {

private:
  
  struct Entry {
    using Key = K;
    const K key;
    const V value;
    static unsigned long hash(const K& k) {return Hash{}(k);}
    bool equal(const K& k) const {return KeyEqual{}(key, k);}
    const K& get_key() const {return key;}
    Entry(const K& k, const V& v) : key(k), value(v) {}
    Entry(const std::pair<Key, V>& kv) : key(kv.first), value(kv.second) {}
    Entry() {}
  };

  using map = parlay_hash<Entry>;
  map m;
  static constexpr auto identity = [] (const Entry& kv) {return kv;};
  static constexpr auto get_value = [] (const Entry& kv) {return kv.value;};
  static constexpr bool default_clear_at_end = false;

public :
  using iterator = typename map::Iterator;
  using key_type = K;
  using mapped_type = V;
  using value_type = std::pair<K, V>;

  parlay_unordered_map(long n, bool clear_at_end = default_clear_at_end) : m(map(n, clear_at_end)) {}

  iterator begin() { return m.begin();}
  iterator end() { return m.end();}
  bool empty() {return size() == 0;}
  bool max_size() {return (1ul << 47)/sizeof(Entry);}
  void clear() {m.clear();}
  long size() { return m.size();}
  long count(const K& k) { return (contains(k)) ? 1 : 0; }
  bool contains(const K& k) { return Find(k).has_value();}

  template <typename F = decltype(get_value)>
  auto Find(const K& k, const F& f = get_value) { return m.Find(k, f); }

  iterator find(const K& k) { return m.find(k); }

  std::pair<iterator,bool> insert(const value_type& entry) {
    return m.insert(Entry(entry));
  }

  template <typename F = decltype(get_value)>
  auto Insert(const K& key, const V& value, const F& f = get_value) {
    return m.Insert(Entry(key, value), f);
  }

  std::optional<Entry> Remove(const K& k) { return m.Remove(k); }

  iterator erase(iterator pos) { return erase(pos); }

  template <typename F>
  bool upsert(const K& k, const F& f) {
    auto g = [&] (std::optional<Entry> entry) {
	       if (entry.has_value())
		 return Entry((*entry).key, f((*entry).value));
	       else return Entry((*entry).key, f(std::nullopt));};
    return m.upsert(k, g);}

  V operator [](const K& k) {
    auto r = Find(k);
    if (r.has_value()) return *r;
    return V();
  }
  
  template <typename F = decltype(identity)>
  parlay::sequence<Entry> entries(const F& f = identity) {
    return m.entries(f);
  }

};

} // namespace parlay
#endif //PARLAYMAP_H_
