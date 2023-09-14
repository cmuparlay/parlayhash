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
  struct atomic {

    using vtype = long;
    static constexpr vtype busy_version = -1;

    std::atomic<vtype> version;
    V val;
    
    atomic(const V& v) : version(0), val(v) {}
    atomic() : version(0) {}

    V load() {
      while (true) {
	vtype ver = version.load();
	V v = val;
	if (ver != busy_version && version.load() == ver)
	  return v;
      }
    }

    void store(const V& v) {
      // Does this need a with_epoch?
      vtype ver = version.load();
      int delay = 100;
      while (true) {
	if (ver == busy_version || version.load() != ver) return;
	if (get_locks().try_lock((long) this, [&] {
	    if (version.load() == ver) {
	      version = busy_version;
	      val = v;
	      version = ver + 1;
	    }
	    return true;})) 
	  return;
	for (volatile int i=0; i < delay; i++);
	delay = std::min(2*delay, 1000);
      }
    }

    bool cas(const V& expected_v, const V& v) {
      vtype ver = version.load();
      int delay = 100;
      bool result = true;
      while (true) {
	V current_v = val;
	if (ver != busy_version && version.load() != ver)
	  return false;
	if (get_locks().try_lock((long) this, [&] {
	    current_v = val;						  
	    if (version.load() != ver ||
		!KeyEqual{}(current_v, expected_v))
	      result = false;
	    else {
	      version = busy_version;
	      val = v;
	      version = ver + 1;
	    }
	    return true;})) 
	  return result;
	for (volatile int i=0; i < delay; i++);
	delay = std::min(2*delay, 1000);
      }
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
