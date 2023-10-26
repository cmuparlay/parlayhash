// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYATOMIC_H_
#define PARLAYATOMIC_H_

#include <optional>
#include "parlay/primitives.h"
#include "parlay/sequence.h"
#include "smr/hazard.h"

namespace parlay {
  template <typename V,
	    class KeyEqual = std::equal_to<V>>
  struct atomic {
    std::atomic<V> val;
    atomic(const V& v) : val(v) {}
    atomic() : val(V{}) {}
    ~atomic() {}
    V load() { return val.load();}
    void store(const V& new_v) { val.store(new_v);}
    bool cas(V expected_v, const V& new_v) {
      return val.compare_exchange_strong(expected_v, new_v);
    }
  };
} // namespace parlay
#endif //PARLAYATOMIC_H_
