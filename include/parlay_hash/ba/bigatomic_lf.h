#pragma once
// A load reads the header, reads the cache, and reads the header again.   If both reads of the header are the same sequence number, return the value from the cache.   If they are both different sequence numbers, then try again, and if either was a pointer, then protected read the value through one of the pointers and return it.   If a ll, return the header as the tag (if a pointer, whichever was used for the value).

// An sc given a tag:
// protected read the header and:
// If the tag was a sequence number, 
//    if the header is not equal to the tag, the sc fails and returns false
//    else copy the new value and tag+1 (new sequence number) to a new object and try to cas this in over the tag (sequence number) in the header
//        if the cas fails, then the sc fails, deletes the object and returns false
//        else copy the value into the cache
//          try to cas tag+1 (new sequence number) into the header
//          if succeeds then retire object and return true
//          else try to install cache again: i.e., 
//            protected read the new header, get value and seq num from it, install value in cache,  and try to cas in seq num 
//            repeat until succeeds (only the sc that swapped out a sequence number will swap one back in so each try will only see a pointer)
// else tag was a pointer
//    if the header is a pointer and different, the sc fails and returns false
//    if the header is a sequence number and does not match the sequence number in the object pointed to by the tag, the sc fails and returns false 
//    otherwise
//       new seq number is 1 + header if header is a sequence number or 1 + object seq number if a pointer
//       copy new value and new seq number to new object and try to cas it in over the tag
//       if the cas fails, the sc fails, deletes the object, and returns false
//       else  if header was a pointer, retire old object 
//          return true

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

  // either a seqnum or a pointer to a backup
  using tag = long;

private:

  struct backup {
    explicit backup(const T& value, long seqnum) : value(value), seqnum(seqnum) { }
    T value;
    long seqnum;
    backup* next_;    // Intrusive link for hazard pointers
    backup* get_next() { return next_; }
    void set_next(backup* next) { next_ = next; }
    void destroy() {  allocator::destroy(this); }
  };

  PARLAY_INLINE
  static tag load_protected(const std::atomic<tag>& src) {
    return get_hazard_list<backup>().protect(src, [](long tag) {
             return is_seqnum(tag) ? nullptr : (backup*) tag; });
  }
  
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
  static backup* new_backup(T v, tag new_seqnum) {
    return allocator::create(v, new_seqnum); }

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

  std::atomic<tag> header;   // Either pointer or sequence number
  alignas(8) char cache[sizeof(T)]; 

 public:

  using value_type = T;
  using allocator = type_allocator<backup>;

  PARLAY_INLINE
  void store_sequential(const T& desired) {
    atomic_store_per_byte_memcpy(&cache, &desired, sizeof(T)); }

  PARLAY_INLINE void load_sequential(char* buffer) {
     atomic_load_per_byte_memcpy(buffer, &cache, sizeof(T));
  }

  big_atomic() : header(std::numeric_limits<long>::min()) {
    static_assert(std::is_default_constructible_v<T>);
    store_sequential(T{});
  }

  big_atomic(const T& initial) : header(std::numeric_limits<long>::min()) {
    store_sequential(initial);
  }

  ~big_atomic() {
    auto hdr = header.load(std::memory_order_relaxed);
    if (is_pointer(hdr)) { Delete(to_ptr(hdr)); }
  }

  PARLAY_INLINE std::pair<T, tag> ll() {
    alignas(T) char buffer[sizeof(T)];
    while (true) {
      tag fst_hdr = header.load(std::memory_order_acquire);
      load_sequential(buffer);
      tag snd_hdr = header.load(std::memory_order_relaxed);
      if (is_seqnum(fst_hdr) && (fst_hdr == snd_hdr)) [[likely]] {
        return {bits_to_object<T>(buffer), fst_hdr};
      } else {
        tag hdr = load_protected(header);
        if (is_pointer(hdr)) 
          return {to_ptr(hdr)->value, hdr};
      }
    }
  }

  PARLAY_INLINE T load() { return ll().first; }

  PARLAY_INLINE bool lv(tag expected_tag) {
    tag hdr = header.load(std::memory_order_acquire);
    if (is_seqnum(expected_tag)) [[likely]] {
      return hdr == expected_tag;
    } else 
      return (expected_tag == hdr ||
              to_ptr(expected_tag)->seqnum == hdr);
  }

  PARLAY_INLINE bool sc(tag expected_tag, const T& v) {
    tag old_hdr, seqnum;
    if (is_seqnum(expected_tag)) [[likely]] {
      old_hdr = header.load(std::memory_order_acquire);
      if (old_hdr != expected_tag) return false;
      seqnum = old_hdr;
    } else { // expected_tag is a pointer
      for (volatile int i = 0; i < 1000; i++); // for efficiency
      old_hdr = header.load(std::memory_order_acquire);
      auto expected_ptr = to_ptr(expected_tag);
      if (is_pointer(old_hdr)) { // also a pointer
        if (expected_tag != old_hdr) return false;
        seqnum = expected_ptr->seqnum;
      } else { // now a tag
        if (old_hdr != expected_ptr->seqnum) return false;
        seqnum = old_hdr;
      }
    }
    tag new_seqnum = seqnum + 1;
    backup* new_ptr = allocator::create(v, new_seqnum);
    protect(new_ptr);

    // try to install new value (linerization point if succeeds)
    tag tmp_hdr = header.load(std::memory_order_relaxed);
    if (tmp_hdr != old_hdr ||
        !header.compare_exchange_strong(tmp_hdr, to_tag(new_ptr))) [[unlikely]] {
      // if failed because current value is a seq number, and old_hdr
      // was a pointer with same seq num, try again             
      if (is_pointer(tmp_hdr) || (tmp_hdr != seqnum) ||
          !header.compare_exchange_strong(tmp_hdr, to_tag(new_ptr))) {
        allocator::destroy(new_ptr); // installation failed
        return false;
      }
    }
    
    if (is_pointer(tmp_hdr)) // was a pointer, do not install cache
      retire(to_ptr(old_hdr));
    else { // try to install the cached value
      store_sequential(v);
      while (header.load(std::memory_order_relaxed) != to_tag(new_ptr) ||
             !header.compare_exchange_weak(to_tag(new_ptr), new_seqnum)) {
        new_ptr = to_ptr(load_protected(header));
        store_sequential(new_ptr->value);
        new_seqnum = new_ptr->seqnum;
      }
      retire(new_ptr);
    }
    return true;
  }

  PARLAY_INLINE bool cas(const T& expected, const T& desired) {
    auto [current, tag] = ll();
    if (!Equal{}(current, expected)) return false;
    if (Equal{}(expected, desired)) return true;
    return sc(tag, desired);
  }

};


}  // namespace parlay
