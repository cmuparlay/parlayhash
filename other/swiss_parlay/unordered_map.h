#ifndef THIRD_PARTY_FLOCK_BENCHMARKS_HASHTABLE_INTERFACES_S_PARLAY_UNORDERED_MAP_H_
#define THIRD_PARTY_FLOCK_BENCHMARKS_HASHTABLE_INTERFACES_S_PARLAY_UNORDERED_MAP_H_

#include <functional>
#include <optional>

#include "swiss_parlay.h" 

template <typename K, typename V, class Hash = std::hash<K>,
          class KeyEqual = std::equal_to<K>>
struct unordered_map {
  using Map = parlay::parlay_unordered_map<K, V, Hash, KeyEqual>;
  Map m;
  unordered_map(long n) : m(Map(n)) {}
  long size() { return m.size(); }
  std::optional<V> find(const K& k) { return m.Find(k); }
  bool insert(const K& key, const V& value) {
    return !m.Insert(key, value).has_value(); }
  template <typename F>
  bool upsert(const K& k, const F& f) { return m.upsert(k, f); }
  bool remove(const K& k) { return m.Remove(k).has_value(); }

  using iterator = typename Map::iterator;
  iterator begin() { return m.begin(); }
  iterator end() { return m.end(); }

  template <typename F>
  void for_each(const F& f) { m.for_each(f); }
};


template <typename K, class Hash = std::hash<K>,
          class KeyEqual = std::equal_to<K>>
struct unordered_set {
  using Set = parlay::parlay_unordered_set<K, Hash, KeyEqual>;
  Set m;
  unordered_set(long n) : m(Set(n)) {}
  long size() { return m.size(); }
  bool find(const K& k) { return m.Find(k); }
  bool insert(const K& key) { return m.Insert(key); }
  bool remove(const K& k) { return m.Remove(k); }

  using iterator = typename Set::iterator;
  iterator begin() { return m.begin(); }
  iterator end() { return m.end(); }

  template <typename F>
  void for_each(const F& f) { m.for_each(f); }
};

#endif  // THIRD_PARTY_FLOCK_BENCHMARKS_HASHTABLE_INTERFACES_S_PARLAY_UNORDERED_MAP_H_
