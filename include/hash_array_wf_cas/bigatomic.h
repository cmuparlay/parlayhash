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
      vtype ver = version.load();
      V v = cache;
      hold* p = ptr.load();
      if (is_valid(ptr.load()) && version.load() == ver)
	return std::pair(p, v);
      p = ptr.load();
      return std::pair(p, remove_mark(p)->get());
    }

    bool try_install(hold* p_old, hold* p_new) {
      hold* p_tmp = p_old;
      if (p_old == ptr.load() &&
	  ptr.compare_exchange_strong(p_old, p_new))
	return true;
      // if failed the first time because the pointer was validated
      // (i.e. with same value) then we need to try again.
      hold* x = ptr.load();
      return (remove_mark(p_tmp) == x &&
	      ptr.compare_exchange_strong(x, p_new));
    }

    void try_load_cache(V v, hold* p, vtype ver) {
      if (!(ver & 1) && ver == version.load() &&
	  version.compare_exchange_strong(ver, ver+1)) {
	cache = v;
	version.store(ver + 2, std::memory_order_relaxed);
	// try to validate the pointer
	ptr.compare_exchange_strong(p, remove_mark(p));
      }
    }

  public:

    atomic(const V& v) : ptr(epoch::memory_pool<hold>::New()), version(0), cache(v) {}
    atomic() : ptr(nullptr), version(0) {}
    ~atomic() {	epoch::memory_pool<hold>::Retire(remove_mark(ptr.load()));}

    V load() {
      vtype ver = version.load();
      V v = cache;
      if (is_valid(ptr.load()) && version.load() == ver)
	return v;
      return epoch::with_epoch([&] { return read().second;});
    }

    bool store(const V& new_v) {
      vtype ver = version.load();
      return epoch::with_epoch([&] {
	auto [old_p, old_v] = read();				 
	hold* new_p = mark_invalid(epoch::memory_pool<hold>::New(new_v));
	if (try_install(old_p, new_p)) {
	  epoch::memory_pool<hold>::Retire(remove_mark(old_p));
	  try_load_cache(new_v, new_p, ver);
	  return true;
	} else {
	  epoch::memory_pool<hold>::Delete(remove_mark(new_p));
	  return false;
	} });
    }

    bool cas(const V& expected_v, const V& new_v) {
      vtype ver = version.load();
      if (KeyEqual{}(expected_v, new_v)) return true;
      return epoch::with_epoch([&] {
	auto [old_p, old_v] = read();				 
	if (!KeyEqual{}(old_v, expected_v))
	  return false;
	hold* new_p = mark_invalid(epoch::memory_pool<hold>::New(new_v));
	if (try_install(old_p, new_p)) {
	  epoch::memory_pool<hold>::Retire(remove_mark(old_p));
	  try_load_cache(new_v, new_p, ver);
	  return true;
	} else {
	  epoch::memory_pool<hold>::Delete(remove_mark(new_p));
	  return false;
	} });
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
