// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYATOMIC_H_
#define PARLAYATOMIC_H_

#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include <parlay/sequence.h>
#include "hazard.h"

namespace parlay {
  
  template <typename V,
	    class KeyEqual = std::equal_to<V>>
  struct atomic {

  private:
    using vtype = long;

    struct hold {
      V val;
      V get() {	return val; } 
      hold(V v) : val(v) {}
      hold() {}
    };
      
    std::atomic<hold*> ptr;
    std::atomic<vtype> version;
    V cache;
    
    // a bit in the pointer is used to mark whether the cache is valid or not
    hold* mark_invalid(hold* ptr) {return (hold*) (((size_t) ptr) | 1ul);}
    hold* remove_mark(hold* ptr) {return (hold*) (((size_t) ptr) & ~1ul);}
    bool is_valid(hold* ptr) {return ((size_t) ptr & 1) == 0;}

    // safely reads assuming inside of a with_epoch
    std::pair<hold*, V> read() {
      vtype ver = version.load(std::memory_order_acquire);
      V v = cache;
      //std::memcpy(&v, &cache, sizeof(V));
      std::atomic_thread_fence(std::memory_order_acquire);
      hold* p = ptr.load();
      // check if value in the cache is valid
      if (is_valid(p) && version.load(std::memory_order_relaxed) == ver)
	return std::pair(p, v);
      // if not, get the value indirectly from p
      return std::pair(p, remove_mark(p)->get());
    }

    bool try_install(hold* p_old, hold* p_new) {
      hold* p_tmp = p_old;
      // try to swap in p_new for p_old
      if (p_old == ptr.load() &&
	  ptr.compare_exchange_strong(p_old, p_new))
	return true;
      // if failed the first time, and this was because p_old was
      // validated (i.e. with the same value) then we need to try
      // again.
      hold* x = ptr.load();
      return (remove_mark(p_tmp) == x &&
	      ptr.compare_exchange_strong(x, p_new));
    }

    void try_load_cache(V v, hold* p, vtype ver) {
      // try to lock the cache
      if (!(ver & 1) && ver == version.load() &&
	  version.compare_exchange_strong(ver, ver+1)) {
	// when locked load the cache
	cache = v;
	std::atomic_thread_fence(std::memory_order_release);
	// unlock the cache
	version.store(ver + 2, std::memory_order_relaxed);
	// try to validate the cache if p has not changed
	ptr.compare_exchange_strong(p, remove_mark(p));
      }
    }

    // try to update the atomic with new_v.  old_p is the current
    // pointer (consistent with the old value), and ver the current
    // version.
    bool try_update(V new_v, hold* old_p, vtype ver) {
      hold* new_p = mark_invalid(epoch::memory_pool<hold>::New(new_v));
      if (try_install(old_p, new_p)) {
	epoch::memory_pool<hold>::Retire(remove_mark(old_p));
	try_load_cache(new_v, new_p, ver);
	return true;
      } else {
	epoch::memory_pool<hold>::Delete(remove_mark(new_p));
	return false;
      }
    }

  public:

    atomic(const V& v) : ptr(epoch::memory_pool<hold>::New()), version(0), cache(v) {}
    atomic() : ptr(nullptr), version(0) {}
    ~atomic() {	epoch::memory_pool<hold>::Retire(remove_mark(ptr.load()));}
    
    V load() {
      vtype ver = version.load(std::memory_order_acquire);
      V v = cache;
      std::atomic_thread_fence(std::memory_order_acquire);
            hold* p = ptr.load();
      // check if value in the cache is valid
      if (is_valid(p) && version.load(std::memory_order_relaxed) == ver)
	return v;
      return epoch::with_announced(&ptr, [&] (hold* p) { return remove_mark(p)->get();});
    }

    void store(const V& new_v) {
      return try_update(new_v, ptr.load(), version.load());
    }

    bool cas(const V& expected_v, const V& new_v) {
      vtype ver = version.load(std::memory_order_acquire);
      return epoch::with_announced(&ptr, [&] (hold* old_p) {
        V old_v = cache;
	// check if value in the cache is valid
	if (!(is_valid(old_p) && version.load(std::memory_order_relaxed) == ver)) 
	  old_v = remove_mark(old_p)->get();
	if (!KeyEqual{}(old_v, expected_v)) return false;
	if (KeyEqual{}(expected_v, new_v)) return true;
	return try_update(new_v, old_p, ver);
	});
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
