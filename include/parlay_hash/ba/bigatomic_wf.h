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
#include <limits>

#include <atomic>
#include <functional>

#include <parlay/alloc.h>

#include "hazard_ptr.h"
#include "utility.h"

namespace parlay {

template<typename T, typename Equal = std::equal_to<>>
struct big_atomic {
  // T must be trivially copyable, but it doesn't have to be trivially default constructible (or
  // even default constructible at all) since we only make copies from what the user gives us

  // Guy: had to comment these checks out to work with parlayhash since it uses std::array
  //static_assert(std::is_trivially_copyable_v<T>);
  //static_assert(std::is_invocable_r_v<bool, Equal, T&&, T&&>);

    // can be either a seqnum_type or an backup*
  // if a seqnum type then negative
  using tag = int64_t; 


 private:
  struct backup {
    explicit backup(const T& value_) : value(value_) { }
    T value;
    backup* next_;    // Intrusive link for hazard pointers
    backup* get_next() { return next_; }
    void set_next(backup* next) { next_ = next; }
    void destroy() {  allocator::destroy(this); }
  };

  static_assert(alignof(backup) >= 2, "Need a spare bit to mark pointers");

  PARLAY_INLINE
  static backup* load_protected(const std::atomic<backup*>& src) {
    return get_hazard_list<backup>().protect(src); }
  
  PARLAY_INLINE
  static void protect(backup* src) {
    get_hazard_list<backup>().protect_direct(src); }

  PARLAY_INLINE
  static void retire(backup* p) {
    if (p) { get_hazard_list<backup>().retire(p); } }

  PARLAY_INLINE
  static void Delete(backup* p) {
    allocator::destroy(p);  }

  PARLAY_INLINE
  static backup* new_backup(T v) {
    return allocator::create(v); }

  PARLAY_INLINE
  static bool is_seqnum(long tag) {
    return tag < 0; }

  PARLAY_INLINE
  static bool is_pointer(long tag) {
    return !is_seqnum(tag); }

  PARLAY_INLINE
  static tag& to_tag(backup*& ptr) {
    return reinterpret_cast<tag&>(ptr); }

  PARLAY_INLINE
  static backup* to_ptr(tag hdr) {
    return reinterpret_cast<backup*>(hdr); }
  
 public:

  using value_type = T;
  using seqnum_type = int64_t;

  using allocator = type_allocator<backup>;

  big_atomic() : indirect(new_backup(T{})),
                 seqnum(std::numeric_limits<int64_t>::min()), cache{} {
    static_assert(std::is_default_constructible_v<T>);
    allocator::init();
    new (static_cast<void*>(&cache)) T{};
  }

  /* implicit */ big_atomic(const T& t) : seqnum(std::numeric_limits<int64_t>::min()),       // NOLINT(google-explicit-constructor)
      indirect(new_backup(t)), cache{} {
    allocator::init();
    new (static_cast<void*>(&cache)) T{t};
  }

  ~big_atomic() {
    auto p = unmark_ptr(indirect.load(std::memory_order_acquire));
    if (p) {
      allocator::destroy(p);
    }
  }

  PARLAY_INLINE
  void store_sequential(const T& desired) {
    atomic_store_per_byte_memcpy(&cache, &desired, sizeof(T)); }

  PARLAY_INLINE void load_sequential(char* buffer) {
    atomic_load_per_byte_memcpy(buffer, &cache, sizeof(T));
  }

  // result tag to the indirect seqnum is protected with a hazard pointer
  PARLAY_INLINE std::pair<T,tag> ll() {
    auto ver = seqnum.load(std::memory_order_acquire);
    alignas(T) char buffer[sizeof(T)];
    load_sequential(buffer);
    auto p = indirect.load();
    if (!is_marked(p) &&
        ver == seqnum.load(std::memory_order_relaxed)) [[likely]]
      return std::pair(bits_to_object<T>(buffer), ver);
    // reload with protection
    p = load_protected(indirect);
    return std::pair<T,tag>(unmark_ptr(p)->value, to_tag(p));
  }

  PARLAY_INLINE bool lv(tag expected_tag) {
    backup* p = indirect.load();
    if (is_seqnum(expected_tag)) [[likely]] { // i.e. a seqnum
      auto ver = seqnum.load(std::memory_order_acquire);
      return (!is_marked(p) && ver == expected_tag);
      } else return (p == to_ptr(expected_tag));
  }

  PARLAY_INLINE bool sc(tag expected_tag, const T& desired) {
    seqnum_type ver;
    backup* p;
    if (is_seqnum(expected_tag)) [[likely]] { // i.e. a seqnum
      p = load_protected(indirect);
      ver = seqnum.load(std::memory_order_acquire);
      if (is_marked(p) || ver != expected_tag) [[unlikely]] return false;
    } else {
      p = to_ptr(expected_tag);
      ver = seqnum.load(std::memory_order_acquire);
      for (volatile int i = 0; i < 500; i++);
    }

    auto ptr = new_backup(desired);
    protect(ptr);
    auto new_p = mark_ptr(ptr);
    auto old_p = p;

    if ((indirect.load(std::memory_order_relaxed) == p &&
         indirect.compare_exchange_strong(p, new_p))
        || (p == indirect.load(std::memory_order_relaxed) &&
            p == unmark_ptr(old_p) &&
            indirect.compare_exchange_strong(p, new_p))) {
      retire(unmark_ptr(p));

      if ((ver % 2 == 0) && ver == seqnum.load(std::memory_order_relaxed) &&
          seqnum.compare_exchange_strong(ver, ver + 1)) {
        store_sequential(desired);
        seqnum.store(ver + 2, std::memory_order_release);
        indirect.compare_exchange_strong(new_p, unmark_ptr(new_p));
      }
      return true;
    }
    Delete(unmark_ptr(new_p));
    return false;
  }

  PARLAY_INLINE T load() { return ll().first; }

  PARLAY_INLINE bool cas(const T& expected, const T& desired) {
    auto [current, tag] = ll();
    if (!Equal{}(current, expected)) return false;
    if (Equal{}(expected, desired)) return true;
    return sc(tag, desired);
  }

 private:

  static constexpr uintptr_t SLOW_MODE = 1;

  static constexpr backup* mark_ptr(backup* p) {
    return reinterpret_cast<backup*>(reinterpret_cast<uintptr_t>(p) | SLOW_MODE); }

  static constexpr backup* unmark_ptr(backup* p) {
    return reinterpret_cast<backup*>(reinterpret_cast<uintptr_t>(p) & ~SLOW_MODE); }

  static constexpr bool is_marked(backup* p) {
    return reinterpret_cast<uintptr_t>(p) & SLOW_MODE; }

  //alignas(std::max_align_t) alignas(T)
  std::atomic<seqnum_type> seqnum;
  alignas(T) char cache[sizeof(T)];  // Over-align in case copies can use faster instructions on aligned data
  std::atomic<backup*> indirect{nullptr};
};


}  // namespace parlay
