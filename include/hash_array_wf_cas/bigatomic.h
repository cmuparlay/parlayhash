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
      size_t x[10];
      //V* next;
      //bool released;
      V get() {
	return val;
	//return *next;
      }
      void release() {
	//if (released) {std::cout << "double release" << std::endl; abort();}
	//released = true;
	//epoch::memory_pool<V>::Retire(next);
      }
      hold(V v)
      : val(v) {}
      // : next(epoch::memory_pool<V>::New(v)) {} //, released(false) {}
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
	epoch::memory_pool<hold>::check_not_corrupted(remove_tag(p));
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
	  epoch::memory_pool<hold>::check_not_corrupted(remove_tag(p));
	  old_v = remove_tag(p)->get();
	}
	if (!KeyEqual{}(old_v, expected_v))
	  return false;
	hold* node = epoch::memory_pool<hold>::New(new_v);
	hold* tagged_node = add_tag(node);
	hold* phold = p;
	if (!ptr.compare_exchange_strong(p, tagged_node))
	  if (remove_tag(phold) != p ||
	      !ptr.compare_exchange_strong(p, tagged_node)) {
	    epoch::memory_pool<hold>::Delete(node);
	    return false;
	  }
	retire_node(p);
        if (!(ver & 1) &&
	    version.compare_exchange_strong(ver,ver+1)) {
	  val = new_v;
	  version.store(ver + 2, std::memory_order_relaxed);
	  if (ptr.compare_exchange_strong(tagged_node, node)) {
	    //node->release();
	    epoch::memory_pool<hold>::Retire(node);
	  }
	}
	return true;});
    }

    void retire_node(hold* p) {
      if (has_tag(p)) {
	//if (p != nullptr) {
	//remove_tag(p)->release();
	epoch::memory_pool<hold>::Retire(remove_tag(p));
      }
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
