#define HASH 1

#include <tbb/concurrent_hash_map.h>

#define USE_SET

template <typename K,
	  typename V,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_map {

  struct HashCompare {
    static size_t hash(const K& k) { return Hash{}(k);}
    static bool equal(const K& k1, const K& k2) { return KeyEqual{}(k1,k2);}
  };

  using Table = tbb::concurrent_hash_map<K, V, HashCompare>;
  Table table;

  std::optional<V> find(const K& k) {
    typename Table::accessor a;
    if (table.find(a, k)) return a->second;
    else return std::optional<V>();
  }

  bool insert(const K& k, const V& v) {
    return table.insert(std::make_pair(k, v));    
  }

  bool remove(const K& k) {
    return table.erase(k);
  }

  unordered_map(size_t n) : table(Table(n)) {}

  long size() {return table.size();}
};

template <typename K,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_set {

  struct HashCompare {
    static size_t hash(const K& k) { return Hash{}(k);}
    static bool equal(const K& k1, const K& k2) { return KeyEqual{}(k1,k2);}
  };

  using Table = tbb::concurrent_hash_map<K, bool, HashCompare>;
  Table table;
  bool find(const K& k) { return table.count(k) > 0;}
  bool insert(const K& k) { return table.insert(std::make_pair(k, true));}
  bool remove(const K& k) { return table.erase(k); }
  unordered_set(size_t n) : table(Table(n)) {}
  long size() {return table.size();}
};
