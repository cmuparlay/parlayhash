// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYHASH_H_
#define PARLAYHASH_H_

#include <atomic>
#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>

namespace parlay {
  
  template <typename K,
	    typename V,
	    class Hash = std::hash<K>,
	    class KeyEqual = std::equal_to<K>>
  struct unordered_map {

    using Voption = std::pair<const bool, const V>;
    using entry = std::atomic<Voption>;

    parlay::sequence<entry> values;
    
    unordered_map(long n) : values(parlay::tabulate<entry>(2*n, [&] (long i) {return Voption(false,0);})) {}

    std::optional<V> find(const K& k) {
      auto [found, v] = values[k].load();
      if (found) return v;
      return {};
    }

    bool insert(const K& k, const V& v) {
      while (true) {
	Voption old_v = values[k].load();
	if (old_v.first) return false;
	else if (values[k].compare_exchange_strong(old_v, Voption(true, v)))
	  return true;
      }
    }
  
    bool remove(const K& k) {
      while (true) {
	Voption old_v = values[k].load();
	if (!old_v.first) return false;
	else if (values[k].compare_exchange_strong(old_v, Voption(false, 0)))
	  return true;
      }
    }

    long size() {
      return parlay::reduce(parlay::map(values, [] (entry& x) {return (long) std::get<0>(x.load());}));
    }

  };

} // namespace parlay
#endif //PARLAYHASH_H_