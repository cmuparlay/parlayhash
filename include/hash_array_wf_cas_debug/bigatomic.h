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
      V get(atomic* ptr) {
	if (loc != ptr) {
	  std::cout << "bad read: " << loc << ", " << ptr << std::endl;
	  abort();
	}
	return val;
      }
      hold(V v, atomic* loc)
	: val(v), loc(loc) {}
      ~hold() {} 
    };
      
    std::atomic<hold*> ptr;
    std::atomic<vtype> version;
    V val;
    
    atomic(const V& v) : ptr(nullptr), version(0), val(v) {}
    atomic() : ptr(nullptr), version(0) {}
    ~atomic() {retire_node(ptr.load());}

    hold* add_invalid_tag(hold* old_ptr, hold* new_ptr) {
      size_t cnt = (((~0ul << 48) & ((size_t) old_ptr)) + (1ul << 49)) | (1ul << 48);
      hold* r = (hold*) (((size_t) new_ptr) | cnt);
      if (is_valid_tag(r)) {std::cout << "invalidate tag error: " << r << std::endl; abort();}
      return r;
    }
    hold* validate_tag(hold* ptr) {
      if (is_valid_tag(ptr)) {std::cout << "validate tag error: " << ptr << std::endl; abort();}
      return (hold*) (((size_t) ptr) + (1ul << 48));
    }
    hold* remove_tag(hold* ptr) {
      return (hold*) (((size_t) ptr) & ((1ul << 48) - 1));
    }
    bool is_valid_tag(hold* ptr) {
      return (((size_t) ptr) & (1ul << 48)) == 0;}

    //hold* add_invalid_tag(hold* ptr) {return (hold*) (((size_t) ptr) | 1ul);}
    //hold* validate_tag(hold* ptr) {return (hold*) (((size_t) ptr) & ~1ul);}
    //hold* remove_tag(hold* ptr) {return (hold*) (((size_t) ptr) & ~1ul);}
    //bool is_valid_tag(hold* ptr) {return 0 == (((size_t) ptr) & 1);}

    std::pair<hold*,V> read() {
      vtype ver = version.load();
      V v = val;
      hold* p = ptr.load();
      vtype ver2 = version.load();
      if (is_valid_tag(p) && ((ver & 1) == 0) && (ver2 == ver))
	return std::pair(p, v);
      hold* p_new = ptr.load();
      hold* p_notag = remove_tag(p_new);
      long e = epoch::get_epoch().get_my_epoch();
      if (!epoch::memory_pool<hold>::check_not_corrupted(p_notag)) {
	std::cout << "in load: " << p << ", " << p_new << ", " << ver << ", "
		  << ver2 << ", " << e << std::endl;
	abort();
      }
      return std::pair(p_new, p_notag->get(this));
    }

    V load() {
      vtype ver = version.load();
      V v = val;
      hold* p = ptr.load();
      vtype ver2 = version.load();
      if (is_valid_tag(p) && ((ver & 1) == 0) && (ver2 == ver)) return v;
      return epoch::with_epoch([&] { return read().second;});
    }

    void try_load_cache(hold* p, vtype ver) {
      if ((ver & 1) == 0 && 
	  version.compare_exchange_strong(ver,ver + 1)) {
	hold* p_notag = remove_tag(p);
	val = p_notag->get(this);
	std::atomic_thread_fence(std::memory_order_seq_cst);
	vtype verp1 = ver + 1;
	if (!version.compare_exchange_strong(verp1, ver + 2)) {
	  std::cout << "unlock failed, setting from: " << ver+1 << ", had value: " << verp1 << std::endl;
	  abort();
	}
	if (ptr.compare_exchange_strong(p, p_notag)) { // try to revalidate
	  // delaying this retire until overwritten, or removing it, fixes the problem
	  // putting a delay loop here does not fix it
	  epoch::memory_pool<hold>::Retire(p_notag);
	}
      }
    }
      
    bool cas(const V& expected_v, const V& new_v) {
      __builtin_prefetch (this);
      return epoch::with_epoch([&] {
	auto [p, v] = read();
	if (!KeyEqual{}(v, expected_v)) return false;
	hold* node = epoch::memory_pool<hold>::New(new_v, this);
	hold* tagged_node = add_invalid_tag(p, node);
	hold* phold = p;
	vtype ver = version.load();
	if (!ptr.compare_exchange_strong(p, tagged_node)) { // invalidate
	  if (is_valid_tag(phold) || validate_tag(phold) != p ||
	      !ptr.compare_exchange_strong(p, tagged_node)) {
	    epoch::memory_pool<hold>::Delete(node);
	    return false;
	  }
	}
	// putting the following delay in anywhere between invalidating and
	// revalidating "fixes" the problem
	//for (volatile int i=0; i < 200; i++);
	try_load_cache(tagged_node, ver);
	retire_node(p);
	return true;});
    }

    void retire_node(hold* p) {
      //if (p != nullptr) {
	if (!is_valid_tag(p)) {
	epoch::memory_pool<hold>::Retire(remove_tag(p));
      } 
    }
  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
