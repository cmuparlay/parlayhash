// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYATOMIC_H_
#define PARLAYATOMIC_H_

#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include "epoch.h"
#include "lock.h"

namespace parlay {
  
  template <typename V,
	    class KeyEqual = std::equal_to<V>>
  struct atomic {

    using vtype = long;
    static constexpr vtype busy_version = -1;

    std::atomic<V*> ptr;
    std::atomic<vtype> version;
    V val;
    
    atomic(const V& v) : ptr(nullptr), version(0), val(v) {}
    atomic() : ptr(nullptr), version(0) {}

    V load() {
      vtype ver = version.load();
      V v = val;
      if (ver != busy_version && version.load() == ver) return v;
      return epoch::with_epoch([&] {
	while (true) {			 
	  vtype ver = version.load();
	  V v = val;
	  if (ver != busy_version && version.load() == ver) return v;
	}});
    }

    bool cas(const V& expected_v, const V& v) {
      __builtin_prefetch (this);
      return epoch::with_epoch([&] {
	vtype ver = version.load();
	bool result = true;
	while (true) {
	  V current_v = val;
	  if (ver != busy_version && version.load() != ver) return false;
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
	      return true;})) {
	    return result;
	  }
	}});
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
