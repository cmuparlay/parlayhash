// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYHASH_H_
#define PARLAYHASH_H_

#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include "bigatomic.h"

namespace parlay {
  
  template <typename K,
	    typename V,
	    class Hash = std::hash<K>,
	    class KeyEqual = std::equal_to<K>>
  struct unordered_map {

    using Voption = std::pair<V,V>;
    using entry = atomic<Voption>;
    
    parlay::sequence<entry> values;
    
    unordered_map(long n) : values(parlay::tabulate<entry>(2*n, [&] (long i) {return Voption(false,0);})) {}

    std::optional<V> find(const K& k) {
      Voption x = values[k].load();
      if (x.first) {if (x.second != k) abort(); return x.second;}
      else return {};
    }

    bool insert(const K& k, const V& v) {
      while (true) {
	Voption old_v = values[k].load();
	if (old_v.first) return false;
	else if (values[k].cas(old_v, Voption(true,k)))
	  return true;
      }
    }

    bool remove(const K& k) {
      while (true) {
	Voption old_v = values[k].load();
	if (!old_v.first) return false;
	else if (values[k].cas(old_v, Voption(false,0)))
	  return true;
      }
    }

    long size() {
      return parlay::reduce(parlay::tabulate(values.size(), [&] (long i) {
							      auto x = values[i].load();
					      if (x.first && x.second != i) abort();
					      return (long) x.first;}));
    }

  };

} // namespace parlay
#endif //PARLAYHASH_H_
