// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYHASH_H_
#define PARLAYHASH_H_

#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include <parlay/internal/concurrency/big_atomic2.h>

namespace parlay {
  
  template <typename K,
	    typename V,
	    class Hash = std::hash<K>,
	    class KeyEqual = std::equal_to<K>>
  struct alignas(64) unordered_map {

    struct Voptionx {
      V first;
      V second;
      constexpr bool operator==(const Voptionx& other) const { return first == other.first && second == other.second; };
    };
    static_assert(std::is_trivially_default_constructible_v<Voptionx>);
    static_assert(std::is_trivially_copyable_v<Voptionx>);
    static_assert(std::is_trivially_destructible_v<Voptionx>);

    using Voption = Voptionx;
    using entry = big_atomic<Voption>;
    
    parlay::sequence<entry> values;
    
    unordered_map(long n) : values(parlay::tabulate<entry>(2*n, [&] (long i) {return Voption{false,0};})) {}

    std::optional<V> find(const K& k) {
      Voption x = values[k].load();
      if (x.first) return x.second;
      else return {};
    }

    bool insert(const K& k, const V& v) {
      while (true) {
	Voption old_v = values[k].load();
	if (old_v.first) return false;
	else if (values[k].cas(old_v, Voption{true,v}))
	  return true;
      }
    }

    bool remove(const K& k) {
      while (true) {
	Voption old_v = values[k].load();
	if (!old_v.first) return false;
	else if (values[k].cas(old_v, Voption{false,0}))
	  return true;
      }
    }

    long size() {
      return parlay::reduce(parlay::map(values, [] (entry& x) {return (long) x.load().first;}));
    }

  };

} // namespace parlay
#endif //PARLAYHASH_H_
