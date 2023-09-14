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
#include "lock.h"

namespace parlay {
  
  template <typename K,
	    typename V,
	    class Hash = std::hash<K>,
	    class KeyEqual = std::equal_to<K>>
  struct unordered_map {
    using Voption = std::pair<bool, V>;
    using entry = Voption;

    parlay::sequence<entry> values;
    
    unordered_map(long n) : values(parlay::tabulate<entry>(2*n, [&] (long i) {return Voption(false,0);})) {}

    std::optional<V> find(const K& k) {
      std::optional<V> result;
      int delay = 5000;
      while (true) {
        if (get_locks().try_lock(k, [&] {
            auto [found, v] = values[k];
	    if (found) result = std::optional(v);
	    return true;}))
	  return result;
	delay = std::min(2*delay, 20000);
	for (volatile int i=0; i < delay; i++);
      }
    }

    bool insert(const K& k, const V& v) {
      bool result = false;
      int delay = 5000;
      while (true) {
        if (get_locks().try_lock(k, [&] {
            if (!values[k].first) {
	      result = true;
	      values[k] = Voption(true,v);
	    }
	    return true;}))
	  return result;
	delay = std::min(2*delay, 20000);
	for (volatile int i=0; i < delay; i++);
      }
    }
  
    bool remove(const K& k) {
      bool result = false;
      int delay = 2000;
      while (true) {
        if (get_locks().try_lock(k, [&] {
            if (values[k].first) {
	      result = true;
	      values[k] = Voption(false,0);
	    }
	    return true;}))
	  return result;
	delay = std::min(2*delay, 100000);
	for (volatile int i=0; i < delay; i++);
      }
    }

    long size() {
      return parlay::reduce(parlay::map(values, [] (entry& x) {return (long) std::get<0>(x);}));
    }

  };

} // namespace parlay
#endif //PARLAYHASH_H_
