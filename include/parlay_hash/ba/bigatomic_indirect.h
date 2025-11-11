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

#include "epoch.h"

namespace parlay {

template<typename V, class KeyEqual = std::equal_to<V>>
struct big_atomic {

  std::atomic<V*> ptr;
  using tag = V*;

  big_atomic(const V& v) : ptr(epoch::New<V>(v)) {}
  big_atomic() : ptr(epoch::New<V>()) {}

  V load() {
    //__builtin_prefetch(this);
    return epoch::with_epoch([&] { return *ptr.load(); });
  }

  void store(const V& v) {
    //__builtin_prefetch(this);
    V* new_v = epoch::New<V>(v);
    V* old_v = ptr.load();
    if (ptr.compare_exchange_strong(old_v, new_v))
      epoch::Retire(old_v);
    else
      epoch::Delete(new_v);
  }

  bool cas(const V& expected_v, const V& v) {
    //__builtin_prefetch(this);
    return epoch::with_epoch([&] {
      V* old_v = ptr.load();
      if (!(*old_v == expected_v)) return false;
      V* new_v = epoch::New<V>(v);
      if (ptr.compare_exchange_strong(old_v, new_v)) {
        epoch::Retire(old_v);
        return true;
      }
      epoch::Delete(new_v);
      return false;
    });
  }


  void store_sequential(const V& v) {
    V* old_v = ptr.load();
    if (old_v != nullptr) epoch::Retire(old_v);
    ptr = epoch::New<V>(v); }

  std::pair<V,tag> ll() {
    return epoch::with_epoch([&] {
      V* old_v = ptr.load();
      return std::pair<V,tag>(*old_v, old_v); });
  }

  bool lv(tag tg) {
    return ptr.load() == tg;
  }

  bool sc(tag expected_tag, const V& v) {
    return epoch::with_epoch([&] {
      V* old_v = ptr.load();
      if (old_v != expected_tag) return false;
      V* new_v = epoch::New<V>(v);
      if (ptr.compare_exchange_strong(old_v, new_v)) {
        epoch::Retire(old_v);
        return true;
      }
      epoch::Delete(new_v);
      return false;
    });
  }

};

}  // namespace parlay
#endif  // PARLAYATOMIC_H_
