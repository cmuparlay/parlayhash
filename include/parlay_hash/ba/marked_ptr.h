#pragma once

#include <cstdint>

#include <type_traits>

namespace parlay {

// A pointer that can be marked and installed with *tagged nullptr* values. Tagged nullptr values
// allow the pointer to logically represent nullptr, i.e., get_ptr() returns nullptr, but secretly
// the value is represented by a 63-bit tag.
//
// If these tags are sequence numbers, then one can create unique nullptrs that do not compare equal
// for the purpose of compare_exchange. That is, they are useful for creating nullptrs that are immune
// to the ABA problem, because one can tell the difference between an old nullptr and a new nullptr.
// This class does not provide the sequence numbers, they must be supplied when constructing the
// tagged nullptr.
//
// All construction is done via factory functions create_ptr and create_tagged_null in order to
// keep marked_ptr as a trivial type.  Marking/unmarking is done via the mark() and unmark()
// member functions, which return a *new marked_ptr*, i.e., they do not mutate in place.
template<typename T>
class marked_ptr {

  static constexpr uintptr_t SEQ_OFFSET = 1;
  static constexpr uintptr_t PTR_OFFSET = 2;

  static constexpr uintptr_t SEQ_MASK = ~((1ULL << SEQ_OFFSET) - 1);
  static constexpr uintptr_t PTR_MASK = ~((1ULL << PTR_OFFSET) - 1);

  static constexpr uintptr_t SEQ_BIT = 1;
  static constexpr uintptr_t MARK_BIT = 1 << 1;

  static_assert((SEQ_MASK & SEQ_BIT) == 0);
  static_assert(alignof(T) >= (MARK_BIT << 1), "Not enough alignment bits to store the marks!");

 public:
  // Factory function -- use instead of constructor so that marked_ptr is a trivial type
  static marked_ptr create_ptr(T* ptr) { return marked_ptr{reinterpret_cast<uintptr_t>(ptr)}; }

  // Factory function for "tagged nullptr".  This is for making successively installed nullptrs
  // compare different to avoid ABA.
  static marked_ptr create_tagged_null(uintptr_t num) { return marked_ptr{(num << SEQ_OFFSET) | SEQ_BIT}; }

  // =============================================== Queries ================================================

  [[nodiscard]] bool is_marked() const noexcept { return ((value & SEQ_BIT)) == 0 && ((value & MARK_BIT) != 0); }

  [[nodiscard]] T* get_ptr() const noexcept {
    return (value & SEQ_BIT) ? nullptr : reinterpret_cast<T*>(value & PTR_MASK);
  }

  T* operator->() const noexcept { return get_ptr(); }
  std::add_lvalue_reference_t<T> operator*() { return *get_ptr(); }

  /* implicit */ operator T*() const noexcept { return get_ptr(); }  // NOLINT(google-explicit-constructor)

  constexpr friend bool operator==(marked_ptr left, marked_ptr right) { return left.value == right.value; }
  constexpr friend bool operator!=(marked_ptr left, marked_ptr right) { return left.value != right.value; }

  // ================================== Updates (all return a new ptr) ======================================

  [[nodiscard]] marked_ptr mark() const noexcept {
    assert(get_ptr() != nullptr);
    return marked_ptr{value | MARK_BIT};
  }

  [[nodiscard]] marked_ptr unmark() const noexcept {
    assert(get_ptr() != nullptr);
    return marked_ptr{value & ~MARK_BIT};
  }

  uintptr_t value;
};

static_assert(std::is_standard_layout_v<marked_ptr<int>> && std::is_trivial_v<marked_ptr<int>>);
static_assert(sizeof(marked_ptr<int>) == 8);

}  // namespace parlay
