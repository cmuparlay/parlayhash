#include "phmap.h"
#define USE_SET

template <typename K,
          typename V,
          class Hash = std::hash<K>,
          class KeyEqual = std::equal_to<K>>
struct unordered_map {
  using Table = phmap::parallel_flat_hash_map<K, V, Hash, KeyEqual, std::allocator<std::pair<const K, V>>, 12, std::mutex>;

  Table table;

  std::optional<V> find(const K& k) {
    V result;
    if (table.if_contains(k, [&](auto&& val) { result = val.second; })) return result;
    else return {};
  }

  bool insert(const K& k, const V& v) {
    return table.try_emplace(k, v).second;
  }

  bool remove(const K& k) {
    return table.erase(k);
  }

  unordered_map(size_t n) {
    table.reserve(n);
  }

  long size() {return table.size();}
};


template <typename K,
          class Hash = std::hash<K>,
          class KeyEqual = std::equal_to<K>>
struct unordered_set {
  using Set = phmap::parallel_flat_hash_set<K, Hash, KeyEqual, std::allocator<K>, 12, std::mutex>;

  Set set;
  bool find(const K& k) {return set.count(k) == 1;}
  bool insert(const K& k) { return set.emplace(k).second; }
  bool remove(const K& k) { return set.erase(k); }
  unordered_set(size_t n) {  set.reserve(n); }
  long size() {return set.size();}
};


