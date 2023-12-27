#ifndef PARLAYSET_H_
#define PARLAYSET_H_

#include "parlay_hash.h"

namespace parlay {
  
template <typename K,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct parlay_unordered_set {

private:
  struct Entry {
    using Key = K;
    const K key;
    static unsigned long hash(const K& k) {return Hash{}(k);}
    bool equal(const K& k) const {return KeyEqual{}(key, k);}
    const K& get_key() const {return key;}
    Entry(const K k) : key(k) {}
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
  using value_type = K;

  parlay_unordered_set(long n, bool clear_at_end = default_clear_at_end) : m(map(n, clear_at_end)) {}

  iterator begin() { return m.begin();}
  iterator end() { return m.end();}
  bool empty() {return size() == 0;}
  bool max_size() {return (1ul << 47)/sizeof(Entry);}
  void clear() {m.clear();}
  long size() { return m.size();}
  long count(const K& k) { return (contains(k)) ? 1 : 0; }
  bool contains(const K& k) { return Find(k).has_value();}

  template <typename F = decltype(get_value)>
  auto Find(const K& k, const F& f = get_value) {
    return m.Find(k, f);
  }

  iterator find(const K& k) { return m.find(k); }

  std::pair<iterator,bool> insert(const value_type& entry) {
    return m.insert(Entry(entry));
  }

  template <typename F = decltype(get_value)>
  auto Insert(const K& key, const F& f = get_value) {
    return m.Insert(Entry(key), f);
  }

  std::optional<Entry> Remove(const K& k) {
    return m.Remove(k);
  }

  iterator erase(iterator pos) {
    return erase(pos);
  }

  template <typename F>
  bool upsert(const K& k, const F& f) {return m.upsert(k, f);}

  V operator [](const K& k) {
    auto r = Find(k);
    if (r.has_value()) return *r;
    return Entry();
  }
  
  template <typename F = decltype(identity)>
  parlay::sequence<Entry> entries(const F& f = identity) {
    return m.entries(f);
  }
};

}
#endif //PARLAYSET_H_
