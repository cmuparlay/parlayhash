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

    struct Voption {
      bool flag;
      V value;
      Voption(bool flag, const V& value) : flag(flag), value(value) {}
      Voption() : flag(false), value(0) {}
      bool operator==(const Voption& o) const {
	return flag == o.flag && value == o.value;};
    };

    struct alignas(64) entry { atomic<Voption> v;};
    
    parlay::sequence<entry> values;
    
    unordered_map(long n) : values(parlay::sequence<entry>(2*n)) {} 

    std::optional<V> find(const K& k) {
      Voption x = values[k].v.load();
      if (x.flag) return x.value;
      else return {};
    }

    bool insert(const K& k, const V& v) {
      while (true) {
	Voption old_v = values[k].v.load();
	if (old_v.flag) return false;
	else if (values[k].v.cas(old_v, Voption(true,v)))
	  return true;
      }
    }

    bool remove(const K& k) {
      while (true) {
	Voption old_v = values[k].v.load();
	if (!old_v.flag) return false;
	else if (values[k].v.cas(old_v, Voption(false,0)))
	  return true;
      }
    }

    long size() {
      return parlay::reduce(parlay::map(values, [] (entry& x) {return (long) x.v.load().flag;}));
    }

  };

} // namespace parlay
#endif //PARLAYHASH_H_
