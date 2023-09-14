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
	vtype ver = version.load();
	V v = val;
	if (ver != busy_version && version.load() == ver) return v;
	return *ptr.load();});
    }

    // void store(const V& v) {
    //   __builtin_prefetch (this);
    //   V* new_v = epoch::memory_pool<V>::New(v);
    //   V* old_v = ptr.load();			 
    //   if (ptr.compare_exchange_strong(old_v, new_v)) 
    // 	epoch::memory_pool<V>::Retire(old_v);
    //   else epoch::memory_pool<V>::Delete(new_v);
    // }

    bool cas(const V& expected_v, const V& v) {
      __builtin_prefetch (this);
      return epoch::with_epoch([&] {
	vtype ver = version.load();
	bool result = true;
	while (true) {
	  V current_v = val;
	  if (ver != busy_version && version.load() != ver) return false;
	  V* node = epoch::memory_pool<V>::New(v);
	  if (get_locks().try_lock((long) this, [&] {
	      current_v = val;						  
	      if (version.load() != ver ||
		  !KeyEqual{}(current_v, expected_v))
		result = false;
	      else {
		ptr = node;
		version = busy_version;
		val = v;
		version = ver + 1;
	      }
	      return true;})) {
	    epoch::memory_pool<V>::Retire(node);
	    return result;
	  }
	  epoch::memory_pool<V>::Delete(node);
	}});
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
