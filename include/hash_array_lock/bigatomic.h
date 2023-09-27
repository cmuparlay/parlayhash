// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYATOMIC_H_
#define PARLAYATOMIC_H_

#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include "lock.h"

namespace parlay {
  
  template <typename V,
	    class KeyEqual = std::equal_to<V>>
  struct alignas(32) atomic {

    V val;
    
    atomic(const V& v) : val(v) {}
    atomic() {}

    V load() {
      V result;
      int delay = 5000;
      while (true) {
        if (get_locks().try_lock((long) this, [&] {
	    result = val;
	    return true;}))
	  return result;
	delay = std::min(2*delay, 50000);
	for (volatile int i=0; i < delay; i++);
      }
    }

    void store(const V& v) {
      int delay = 5000;
      while (true) {
        if (get_locks().try_lock((long) this, [&] {
	    val = v;
	    return true;}))
	  return;
	delay = std::min(2*delay, 50000);
	for (volatile int i=0; i < delay; i++);
      }
    }


    bool cas(const V& expected_v, const V& v) {
      bool result = true;
      int delay = 5000;
      while (true) {
        if (get_locks().try_lock((long) this, [&] {
	    if (!KeyEqual{}(val, expected_v))
	      result = false;
	    else val = v;
	    return true;}))
	  return result;
	delay = std::min(2*delay, 50000);
	for (volatile int i=0; i < delay; i++);
      }
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
