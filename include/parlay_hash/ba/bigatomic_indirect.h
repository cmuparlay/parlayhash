// An implementation of big_atomic using indirect values with Hazard-Pointer reclamation.
//
//  Supports:
//  - Wait-free load
//  - Wait-free store
//  - Wait-free CAS (with spurious failures in the presence of stores)
//
// Uses up to O(n + p^2) extra space.
//

#ifndef PARLAYATOMIC_H_
#define PARLAYATOMIC_H_

#include <atomic>
#include <functional>

#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include <parlay/portability.h>

#include "hazard.h"

namespace parlay {

template<typename V, class KeyEqual = std::equal_to<V>>
struct big_atomic {

  std::atomic<V*> ptr;

  big_atomic(const V& v) : ptr(hazard::New<V>(v)) {}
  big_atomic() : ptr(hazard::New<V>(V{})) {}
  ~big_atomic() { hazard::Delete(ptr.load()); }

  
  using tag = V*;

  PARLAY_INLINE void store_sequential(const V& v) {
    auto old_v = ptr.load();
    if (old_v != nullptr) hazard::Retire(old_v);
    ptr = hazard::New<V>(v); }

  PARLAY_INLINE std::pair<V,tag> ll() {
    __builtin_prefetch(this);
    auto old_v = hazard::load_protected(ptr, 0);
    return std::pair<V,tag>(*old_v, old_v);
  }

  PARLAY_INLINE bool lv(tag tg) {
    return ptr.load() == tg;
  }

  PARLAY_INLINE bool sc(tag expected_tag, const V& v) {
      auto old_v = ptr.load();
      if (old_v != expected_tag) return false;
      auto new_v = hazard::New<V>(v);
      if (ptr.compare_exchange_strong(old_v, new_v)) {
        hazard::Retire(old_v);
        return true;
      }
      hazard::Delete(new_v);
      return false;
  }

  PARLAY_INLINE V load() { return ll().first; }

  PARLAY_INLINE bool cas(const V& expected, const V& desired) {
    auto [current, tag] = ll();
    if (!KeyEqual{}(current, expected)) return false;
    if (KeyEqual{}(expected, desired)) return true;
    return sc(tag, desired);
  }
};

}  // namespace parlay
#endif  // PARLAYATOMIC_H_
