// An implementation of big_atomic using a SeqLock & indirect backup values with Hazard-Pointer reclamation.
//
//  Supports:
//  - Wait-free load
//  - Wait-free store
//  - Wait-free CAS (with spurious failures in the presence of stores)
//
// Uses up to O(n + p^2) extra space.  Uses the Parlay allocator.
//

#pragma once

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>

#include <atomic>
#include <functional>

#include <parlay/alloc.h>

#include "utility.h"
#include "hazard_ptr.h"

namespace parlay {

template<typename T, typename Equal = std::equal_to<>>
struct big_atomic {
  // T must be trivially copyable, but it doesn't have to be trivially default constructible (or
  // even default constructible at all) since we only make copies from what the user gives us
  //static_assert(std::is_trivially_copyable_v<T>);
  //static_assert(std::is_invocable_r_v<bool, Equal, T&&, T&&>);

 private:
  struct indirect_holder {
    explicit indirect_holder(const T& value_) : value(value_) { }
    T value;
    indirect_holder* next_;    // Intrusive link for hazard pointers

    indirect_holder* get_next() {
      return next_;
    }

    void set_next(indirect_holder* next) {
      next_ = next;
    }

    void destroy() {
      allocator::destroy(this);
    }
  };

  static_assert(alignof(indirect_holder) >= 2, "Need a spare bit to mark pointers");

 public:

  using value_type = T;
  using version_type = long;

  using allocator = type_allocator<indirect_holder>;

  big_atomic() : indirect_value(allocator::create(T{})), version(0), fast_value{} {
    static_assert(std::is_default_constructible_v<T>);

    // force correct static initialization order
    allocator::init();
    hazptr_instance();

    new (static_cast<void*>(&fast_value)) T{};
  }

  /* implicit */ big_atomic(const T& t) : version(0),       // NOLINT(google-explicit-constructor)
      indirect_value(allocator::create(t)), fast_value{} {
    // force correct static initialization order
    allocator::init();
    hazptr_instance();

    new (static_cast<void*>(&fast_value)) T{t};
  }

  PARLAY_INLINE T load() {
    auto ver = version.load(std::memory_order_acquire);
    alignas(T) char buffer[sizeof(T)];
    atomic_load_per_byte_memcpy(&buffer, &fast_value, sizeof(T));
    auto p = indirect_value.load();
    if (!is_marked(p) &&
        ver == version.load(std::memory_order_relaxed)) [[likely]]
      return bits_to_object<T>(buffer);

    return load_indirect(p);
  }

  // side effects p
  PARLAY_INLINE T load_indirect(indirect_holder* & p) {
    auto hazptr = hazptr_holder{};
    p = hazptr.protect(indirect_value);
    assert(unmark_ptr(p) != nullptr);
    // Readers can help put the object back into "fast mode".  This is very good if updates
    // are infrequent since this will speed up all subsequent reads.  Unfortunately this
    // could be a severe slowdown if updates are very frequent, since many reads will try
    // to help and waste work here...  Might be nice to optimize this so that it doesn't
    // try to help every time, but only every once in a while.
    //if (is_marked(p)) {
    //  try_seqlock_and_store(version.load(std::memory_order_relaxed), unmark_ptr(p)->value, p);
    //}
    return unmark_ptr(p)->value;
  }

  PARLAY_INLINE void store(const T& desired) {
    auto num = version.load(std::memory_order_acquire);
    auto new_p = mark_ptr(allocator::create(desired));
    auto old_p = indirect_value.exchange(new_p);
    retire(unmark_ptr(old_p));
    try_seqlock_and_store(num, desired, new_p);
  }

  PARLAY_INLINE bool cas(const T& expected, const T& desired) {
    auto ver = version.load(std::memory_order_acquire);
    alignas(T) char buffer[sizeof(T)];
    atomic_load_per_byte_memcpy(&buffer, &fast_value, sizeof(T));

    auto hazptr = hazptr_holder{};
    auto p = hazptr.protect(indirect_value);
    assert(unmark_ptr(p) != nullptr);

    T current = [&]() {  // Use IIFE since you can't stick [[likely]] on a ternary statement
      if (!is_marked(p) && ver == version.load(std::memory_order_relaxed)) [[likely]]
        return bits_to_object<T>(buffer);
      else
        return unmark_ptr(p)->value;
    }();

    if (!Equal{}(current, expected)) return false;
    if (Equal{}(expected, desired)) return true;

    auto xx = allocator::create(desired);
    hazptr.protect_direct(xx);
    auto new_p = mark_ptr(xx);
    auto old_p = p;

    if ((indirect_value.load(std::memory_order_relaxed) == p && indirect_value.compare_exchange_strong(p, new_p))
        || (p == indirect_value.load(std::memory_order_relaxed) && p == unmark_ptr(old_p) && indirect_value.compare_exchange_strong(p, new_p))) {

      retire(unmark_ptr(p));
      try_seqlock_and_store(ver, desired, new_p);
      hazptr.unprotect_direct(xx);
      return true;
    }
    else {
      allocator::destroy(unmark_ptr(new_p));
      hazptr.unprotect_direct(xx);
      return false;
    }
  }

  using tag = indirect_holder*; 

  void store_sequential(const T& desired) {
    atomic_store_per_byte_memcpy(&fast_value, &desired, sizeof(T)); }

  PARLAY_INLINE bool lv(tag tg) {
    return indirect_value.load() == tg;
  }

  PARLAY_INLINE std::pair<T,tag> ll() {
    auto ver = version.load(std::memory_order_acquire);
    alignas(T) char buffer[sizeof(T)];
    atomic_load_per_byte_memcpy(&buffer, &fast_value, sizeof(T));
    auto p = indirect_value.load();
    if (!is_marked(p) &&
        ver == version.load(std::memory_order_relaxed)) [[likely]]
                                                          return std::pair(bits_to_object<T>(buffer), p);

    return std::pair<T,tag>(load_indirect(p), p);
  }

  PARLAY_INLINE bool sc(tag expected_tag, const T& desired) {
    auto ver = version.load(std::memory_order_acquire);
    alignas(T) char buffer[sizeof(T)];
    atomic_load_per_byte_memcpy(&buffer, &fast_value, sizeof(T));

    auto hazptr = hazptr_holder{};
    auto p = hazptr.protect(indirect_value);
    assert(unmark_ptr(p) != nullptr);

    T current = [&]() {  // Use IIFE since you can't stick [[likely]] on a ternary statement
                  if (!is_marked(p) && ver == version.load(std::memory_order_relaxed)) [[likely]]
                                                                                         return bits_to_object<T>(buffer);
                  else
                    return unmark_ptr(p)->value;
                }();

    if (p != expected_tag) return false; // SC: this line changed
    // if (Equal{}(expected, desired)) return true; // SC: this line removed

    auto xx = allocator::create(desired);
    hazptr.protect_direct(xx);
    auto new_p = mark_ptr(xx);
    auto old_p = p;

    if ((indirect_value.load(std::memory_order_relaxed) == p && indirect_value.compare_exchange_strong(p, new_p))
        || (p == indirect_value.load(std::memory_order_relaxed) && p == unmark_ptr(old_p) && indirect_value.compare_exchange_strong(p, new_p))) {

      retire(unmark_ptr(p));
      try_seqlock_and_store(ver, desired, new_p);
      hazptr.unprotect_direct(xx);
      return true;
    }
    else {
      allocator::destroy(unmark_ptr(new_p));
      hazptr.unprotect_direct(xx);
      return false;
    }
  }

  ~big_atomic() {
    auto p = unmark_ptr(indirect_value.load(std::memory_order_acquire));
    if (p) {
      allocator::destroy(p);
    }
  }

 private:

  void try_seqlock_and_store(version_type num, const T& desired, indirect_holder* p) noexcept {
    if ((num % 2 == 0) && num == version.load(std::memory_order_relaxed) && version.compare_exchange_strong(num, num + 1)) {
      atomic_store_per_byte_memcpy(&fast_value, &desired, sizeof(T));
      version.store(num + 2, std::memory_order_release);
      indirect_value.compare_exchange_strong(p, unmark_ptr(p));
    }
  }

  struct hazptr_holder {
    indirect_holder* protect(const std::atomic<indirect_holder*>& src) const {
      return hazptr_instance().protect(src);
    }
    void protect_direct(indirect_holder* src) const {
      hazptr_instance().protect_direct(src);
    }
    void unprotect_direct(indirect_holder* src) const {
      hazptr_instance().unprotect_direct(src);
    }
  };

  static void retire(indirect_holder* p) {
    if (p) {
      hazptr_instance().retire(p);
    }
  }

  static HazardPointers<indirect_holder>& hazptr_instance() {
    return get_hazard_list<indirect_holder>();
  }

  static constexpr uintptr_t SLOW_MODE = 1;

  static constexpr indirect_holder* mark_ptr(indirect_holder* p) { return reinterpret_cast<indirect_holder*>(reinterpret_cast<uintptr_t>(p) | SLOW_MODE); }
  static constexpr indirect_holder* unmark_ptr(indirect_holder* p) { return reinterpret_cast<indirect_holder*>(reinterpret_cast<uintptr_t>(p) & ~SLOW_MODE); }
  static constexpr bool is_marked(indirect_holder* p) { return reinterpret_cast<uintptr_t>(p) & SLOW_MODE; }

  std::atomic<indirect_holder*> indirect_value{nullptr};
  std::atomic<version_type> version;
  alignas(std::max_align_t) alignas(T) char fast_value[sizeof(T)];  // Over-align in case copies can use faster instructions on aligned data
};


}  // namespace parlay
