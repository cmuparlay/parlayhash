#include "phmap.h"

template <typename K,
          typename V,
          class Hash = std::hash<K>,
          class KeyEqual = std::equal_to<K>>
struct unordered_map {
  using Table = phmap::parallel_flat_hash_map_m<K, V, Hash, KeyEqual>;

  Table table;

  std::optional<V> find(const K& k) {
    V result;
    if (table.if_contains(k, [&](auto&& val) { result = val.second; })) return result;
    else return {};
  }

  bool insert(const K& k, const V& v) {
    return table.try_emplace_l(k, [](auto&&) {}, v);
  }

  bool remove(const K& k) {
    return table.erase(k);
  }

  unordered_map(size_t n) {
    table.reserve(n);
  }

  long size() {return table.size();}
};


