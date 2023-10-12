// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYATOMIC_H_
#define PARLAYATOMIC_H_

#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include "smr/lock.h"

namespace parlay {
  
  template <typename V,
	    class KeyEqual = std::equal_to<V>>
  struct atomic {

    using vtype = long;

    std::atomic<vtype> version;
    V val;
    
    atomic(const V& v) : version(0), val(v) {}
    atomic() : version(0) {}

    V load() {
      while (true) {
	vtype ver = version.load(std::memory_order_acquire);
	V v = val;
	std::atomic_thread_fence(std::memory_order_acquire);
	if ((ver & 1) == 0 && version.load(std::memory_order_relaxed) == ver)
	  return v;
      }
    }

    void store(const V& v) {
      vtype ver = version.load();
      int delay = 100;
      if (ver & 1) {
	while (ver == version.load());
	return;
      }
      while (true) {
	if (get_locks().try_lock((long) this, [&] {
	    if (version.load() == ver) {
	      version.store(ver + 1, std::memory_order_relaxed);
	      std::atomic_thread_fence(std::memory_order_release);
	      val = v;
	      version.store(ver + 2, std::memory_order_release);
	    }
	    return true;})) 
	  return;
	if (version.load() > ver + 1) return;
	for (volatile int i=0; i < delay; i++);
	delay = std::min(2*delay, 1000);
      }
    }

    bool cas(const V& expected_v, const V& v) {
      vtype ver = version.load();
      bool result = true;
      int delay = 100;
      if (ver & 1) {
	while (ver == version.load(std::memory_order_acquire));
	return false;
      }
      while (true) {
	if (get_locks().try_lock((long) this, [&] {
	    V current_v = val;						  
	    if (version.load(std::memory_order_acquire) != ver
		|| !(current_v == expected_v))
	      result = false;
	    else if (expected_v == v) return true;
	    else {
	      version.store(ver + 1, std::memory_order_relaxed);
	      std::atomic_thread_fence(std::memory_order_release);
	      val = v;
	      version.store(ver + 2, std::memory_order_release);
	    }
	    return true;})) 
	  return result;
	if (version.load() > ver + 1) return false;
	for (volatile int i=0; i < delay; i++);
	delay = std::min(2*delay, 1000);
      }
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
