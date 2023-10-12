// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYATOMIC_H_
#define PARLAYATOMIC_H_

#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include "smr/epoch.h"

namespace parlay {
  
  template <typename V,
	    class KeyEqual = std::equal_to<V>>
  struct atomic {

    std::atomic<V*> ptr;
    
    atomic(const V& v) : ptr(epoch::New<V>(v)) {}
    atomic() : ptr(epoch::New<V>()) {}

    V load() {
      __builtin_prefetch (this);
      return epoch::with_epoch([&] {return *ptr.load();});
    }

    void store(const V& v) {
      __builtin_prefetch (this);
      V* new_v = epoch::New<V>(v);
      V* old_v = ptr.load();			 
      if (ptr.compare_exchange_strong(old_v, new_v)) 
	epoch::Retire(old_v);
      else epoch::Delete(new_v);
    }

    bool cas(const V& expected_v, const V& v) {
      __builtin_prefetch (this);
      return epoch::with_epoch([&] {
	V* old_v = ptr.load();
	if (!(*old_v == expected_v))
	  return false;
	V* new_v = epoch::New<V>(v);
	if (ptr.compare_exchange_strong(old_v, new_v)) {
	  epoch::Retire(old_v);
	  return true;
	}
	epoch::Delete(new_v);
	return false;});
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
