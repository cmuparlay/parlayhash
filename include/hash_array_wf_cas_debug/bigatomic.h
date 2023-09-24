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
      const V val;
      atomic* loc;
      vtype version;
      V get(atomic* ptr) {
	if (loc != ptr) {
	  std::cout << "bad read: " << loc << ", " << ptr << std::endl;
	  abort();
	}
	return val;
      }
      void release(atomic* ptr) {}
      hold(V v, atomic* loc, vtype version)
	: val(v), loc(loc), version(version) {}
      ~hold() {} 
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
      // vtype ver = version.load();
      // std::atomic_thread_fence(std::memory_order_seq_cst);
      // V v = val;
      // std::atomic_thread_fence(std::memory_order_seq_cst);
      // if (!has_tag(ptr.load()) && version.load() == ver) return v;
      return epoch::with_epoch([&] {
				 long e = epoch::get_epoch().get_my_epoch();
	vtype ver = version.load();
	//std::atomic_thread_fence(std::memory_order_seq_cst);
	V v = val;
	//std::atomic_thread_fence(std::memory_order_seq_cst);
	hold* p = ptr.load();
	vtype ver2 = version.load();
	if (!has_tag(p) && ver2 == ver) return v;
	hold* p_new = ptr.load();
	hold* p_notag = remove_tag(p_new);
	if (!epoch::memory_pool<hold>::check_not_corrupted(p_notag)) {
	  std::cout << "in load: " << p << ", " << p_new << ", " << ver << ", " << ver2 << ", " << e << ", " << p_notag->version << std::endl;
	  abort();
	}
	return p_notag->get(this);});
    }

    bool cas(const V& expected_v, const V& new_v) {
      __builtin_prefetch (this);
      return epoch::with_epoch([&] {
 	vtype ver = version.load();
	//std::atomic_thread_fence(std::memory_order_seq_cst);
	V old_v = val;
	//std::atomic_thread_fence(std::memory_order_seq_cst);
	hold* p = ptr.load();
	vtype ver2 = version.load();
	bool from_ptr = has_tag(p) || (ver2 != ver);
	if (has_tag(p) || (ver2 != ver)) {
	  p = ptr.load();
	  if (!epoch::memory_pool<hold>::check_not_corrupted(remove_tag(p))) {
	    std::cout << "in cas" << std::endl;
	    abort();
	  }
	  old_v = remove_tag(p)->get(this);
	}
	if (!KeyEqual{}(old_v, expected_v))
	  return false;
	hold* node = epoch::memory_pool<hold>::New(new_v, this, ver+2);
	hold* tagged_node = add_tag(node);
	hold* phold = p;
	if (!ptr.compare_exchange_strong(p, tagged_node))
	  if (remove_tag(phold) != p ||
	      !ptr.compare_exchange_strong(p, tagged_node)) {
	    epoch::memory_pool<hold>::Delete(node);
	    return false;
	  }
	//if (from_ptr && remove_tag(phold)->get() != expected_v) abort();
	retire_node(p);
        if (!(ver & 1) &&
	    version.compare_exchange_strong(ver,ver+1)) {
	  //std::atomic_thread_fence(std::memory_order_seq_cst);
	  val = new_v;
	  //std::atomic_thread_fence(std::memory_order_seq_cst);
	  version.store(ver + 2, std::memory_order_relaxed);
	  if (ptr.compare_exchange_strong(tagged_node, node)) {
	    epoch::memory_pool<hold>::Retire(node);
	    //node->release(this);
	  }
	}
	return true;});
    }

    void retire_node(hold* p) {
      //if (p != nullptr) {
      //remove_tag(p)->release(this);
      //}
      if (has_tag(p)) {
      //remove_tag(p)->release();
	epoch::memory_pool<hold>::Retire(remove_tag(p));
      }
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
