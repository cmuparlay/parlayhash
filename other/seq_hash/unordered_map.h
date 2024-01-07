#pragma once

#define USE_SET

#include <seq/seq/concurrent_map.hpp>

template <typename K,
	  typename V,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_map {

  using Table = seq::concurrent_map<K, V, Hash, KeyEqual, std::allocator<std::pair<K,V>>, seq::high_concurrency>;
  Table table;
  std::optional<V> find(const K& k) {
    std::optional<V> result;
    table.visit(k, [&](auto&& x) { result = x.second; });
    return result;
  }
  bool insert(const K& k, const V& v) { return table.emplace(k, v); }
  bool remove(const K& k) { return table.erase(k); }
  unordered_map(size_t n) : table(n) {}
  long size() {return table.size();}
};

template <typename K,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_set {
  using Set = seq::concurrent_set<K, Hash, KeyEqual, std::allocator<K>, seq::high_concurrency>;
  Set set;
  bool find(const K& k) { return set.count(k) > 0;}
  bool insert(const K& k) { return set.emplace(k); }
  bool remove(const K& k) { return set.erase(k); }
  unordered_set(size_t n) { }
  long size() {return set.size();}
};

