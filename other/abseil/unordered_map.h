#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"

#define USE_SET

template <typename K,
	  typename V,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_map {

  using Table = absl::flat_hash_map<K, V, Hash, KeyEqual>;
  Table table;

  std::optional<V> find(const K& k) {
    auto r = table.find(k);
    if (r != table.end()) return (*r).second;
    else return std::optional<V>();
  }

  bool insert(const K& k, const V& v) {
    return table.insert(std::make_pair(k, v)).second;    
  }

  bool remove(const K& k) {
    return table.erase(k) == 1;
  }

  unordered_map(size_t n) : table(Table(n)) {}

  long size() {return table.size();}
};

template <typename K,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_set {
  using Set = absl::flat_hash_set<K, Hash, KeyEqual>;
  Set set;
  bool find(const K& k) { return set.count(k) > 0; }
  bool insert(const K& k) { return set.insert(k).second;}
  bool remove(const K& k) { return set.erase(k) == 1; }
  unordered_set(size_t n) : set(Set(n)) {}
  long size() {return set.size();}
};
