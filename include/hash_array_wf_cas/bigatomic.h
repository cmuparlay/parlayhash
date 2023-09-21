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

    std::atomic<V*> ptr;
    std::atomic<vtype> version;
    V val;
    
    atomic(const V& v) : ptr(nullptr), version(0), val(v) {}
    atomic() : ptr(nullptr), version(0) {}

    V* add_tag(V* ptr) {return (V*) (((size_t) ptr) | 1ul);}
    V* remove_tag(V* ptr) {return (V*) (((size_t) ptr) & ~1ul);}
    bool has_tag(V* ptr) {return (size_t) ptr & 1;}
    
    V load() {
      vtype ver = version.load();
      V v = val;
      if (!has_tag(ptr.load()) && version.load() == ver) return v;
      return epoch::with_epoch([&] {
	vtype ver = version.load();
	V v = val;
	if (!has_tag(ptr.load()) && version.load() == ver) return v;
	return *remove_tag(ptr.load());});
    }

    bool cas(const V& expected_v, const V& new_v) {
      __builtin_prefetch (this);
      return epoch::with_epoch([&] {
 	vtype ver = version.load();
	V old_v = val;
	V* p = ptr.load();
	if (has_tag(p) || version.load() != ver)
	  old_v = *remove_tag(p);
	if (!KeyEqual{}(old_v, expected_v))
	  return false;
	V* node = epoch::memory_pool<V>::New(new_v);
	V* tagged_node = add_tag(node);
	if (!ptr.compare_exchange_strong(p, tagged_node)) {
	  epoch::memory_pool<V>::Delete(node);
	  return false;
	}
	if (has_tag(p))
	  epoch::memory_pool<V>::Retire(remove_tag(p));
        if (!(ver & 1) &&
	    version.compare_exchange_strong(ver,ver+1)) {
	  val = new_v;
	  version = ver + 2;
	  if (ptr.compare_exchange_strong(tagged_node, node))
	    epoch::memory_pool<V>::Retire(node);
	}
	return true;});
    }

  };

} // namespace parlay
#endif //PARLAYATOMIC_H_
