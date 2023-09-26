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

    using vtype = long;

    struct hold {
      V val;
      V get() {	return val; } 
      hold(V v) : val(v) {}
    };
      
    std::atomic<hold*> ptr;
    std::atomic<vtype> version;
    V val;
    
    atomic(const V& v) : ptr(nullptr), version(0), val(v) {}
    atomic() : ptr(nullptr), version(0) {}
    ~atomic() {retire_node(ptr.load());}

    hold* add_tag(hold* ptr) {return (hold*) (((size_t) ptr) | 1ul);}
    hold* remove_tag(hold* ptr) {return (hold*) (((size_t) ptr) & ~1ul);}
    bool has_tag(hold* ptr) {return (size_t) ptr & 1;}
    
    V load() {
      vtype ver = version.load();
      V v = val;
      if (!has_tag(ptr.load()) && version.load() == ver) return v;
      return epoch::with_epoch([&] {
	vtype ver = version.load();
	V v = val;
	if (!has_tag(ptr.load()) && version.load() == ver) return v;
	hold* p = ptr.load();
	return remove_tag(p)->get();});
    }

    bool cas(const V& expected_v, const V& new_v) {
      __builtin_prefetch (this);
      return epoch::with_epoch([&] {
 	vtype ver = version.load();
	V old_v = val;
	hold* p = ptr.load();
	if (has_tag(p) || version.load() != ver) {
	  p = ptr.load();
	  old_v = remove_tag(p)->get();
	}
	if (!KeyEqual{}(old_v, expected_v))
	  return false;
	hold* node = epoch::memory_pool<hold>::New(new_v);
	hold* tagged_node = add_tag(node);
	hold* phold = p;
	if (!(p == ptr.load() && ptr.compare_exchange_strong(p, tagged_node))) {
	  hold* x = ptr.load();
	  if (remove_tag(phold) != x ||
	      !ptr.compare_exchange_strong(x, tagged_node)) {
	    epoch::memory_pool<hold>::Delete(node);
	    return false;
	  }
	}
	retire_node(p);
        if (!(ver & 1) &&
	    ver == version.load() &&
	    version.compare_exchange_strong(ver, ver+1)) {
	  val = new_v;
	  version.store(ver + 2, std::memory_order_relaxed);
	  ptr.compare_exchange_strong(tagged_node, node);
	}
	return true;});
    }

    void retire_node(hold* p) {
      if (p != nullptr) {
	epoch::memory_pool<hold>::Retire(remove_tag(p));
      }
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
