
#include "parlay_hash/unordered_map.h"

template <typename K,
	  typename V,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_map {

  using Map = parlay_unordered_map<K,V,Hash,KeyEqual>;
  Map m;
  unordered_map(long n) : m(Map(n)) {}
  long size() { return m.size();}

  std::optional<V> find(const K& k) { return m.Find(k); }

  bool insert(const K& key, const V& value) {
    return !m.Insert(key, value).has_value();
  }

  template <typename F>
  bool upsert(const K& k, const F& f) {return m.upsert(k, f);}
  
  bool remove(const K& k) {
    return m.Remove(k).has_value();
  }
};
    
