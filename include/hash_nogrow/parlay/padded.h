// MIT license (https://opensource.org/license/mit/)
// Initial Author: Daniel Anderson
// Developed as part of cmuparlay/parlaylib

#ifndef PARLAY_ALLOCATORS_PADDED_H
#define PARLAY_ALLOCATORS_PADDED_H

/*
    Padded types for avoiding false sharing by over-aligning to a cache-line boundary.

    parlay::padded<T> should be a drop-in replacement for T in just about any scenario,
    without having to change the code that makes use of the T object. padded<T> can be
    initialized with any initializer that would work on T, including copy and move
    initialization, and any constructor of T. Assignment operations should also work.

    You can also bind a padded<T> to const/non-const reference/rvalue-reference variables
    of type T, e.g.,

      padded<int> p{1};
      int& x = p;  // refers to the padded int 1
      x = 2;       // p now contains 2

    This also applies to function parameters. For class types, you should also be able
    to invoke overloaded operations and member functions, e.g.,

      padded<std::vector<int>> v{1,2,3};
      v.push_back(4);
      v[0] = 42;

    You can even invoke function pointers!!

      padded<int(*)()> fp = &func;
      int x = fp();

    The only thing that doesn't seem to work is directly invoking member-function pointers...

 */

// Padded types to avoid false sharing. Takes a type T and makes its size
// at least Size bytes by over-aligning it. Size must be a valid alignment.
namespace parlay {
namespace allocators {

// Obtains a pointer to an object of type T located at the address represented
// by p. Essentially performs std::launder(reinterpret_cast<T*>(p)).
template<typename T>
[[nodiscard]] constexpr T* from_bytes(std::byte* p) noexcept {
  // std::launder not available on older compilers
#ifdef __cpp_lib_launder
  return std::launder(reinterpret_cast<T*>(p));
#else
  return reinterpret_cast<T*>(p);
#endif
}

template<typename T, size_t Size = 128, typename Sfinae = void>
struct padded;

// Use user-defined conversions to pad primitive types
template<typename T, size_t Size>
struct alignas(Size) padded<T, Size, typename std::enable_if_t<std::is_scalar_v<T>>> {
  padded() : x{} {};
  /* implicit */ padded(T _x) : x(_x) { }       // cppcheck-suppress noExplicitConstructor    // NOLINT
  /* implicit */ operator T&() & { return x; }                                                // NOLINT
  /* implicit */ operator const T&() const& { return x; }                                     // NOLINT
  /* implicit */ operator T&&() && { return std::move(x); }                                   // NOLINT
  /* implicit */ operator const T&&() const&& { return std::move(x); }                        // NOLINT

  // Allow padded function pointers to be directly invoked!
  template<typename... Ts> auto operator()(Ts... args) const noexcept(std::is_nothrow_invocable_v<T, Ts...>)
      -> std::enable_if_t<std::is_invocable_v<T, Ts...>, std::invoke_result_t<T, Ts...>> {
    return x(std::forward<Ts>(args)...);
  }

  // Note: I couldn't figure out a way to make member-function pointers directly invocable :(

  T x;
};

// Use inheritance to pad class types
template<typename T, size_t Size>
struct alignas(Size) padded<T, Size, typename std::enable_if_t<std::is_class_v<T>>> : public T {
  static_assert(std::is_same_v<T, std::remove_cv_t<T>>,
      "padded<T> requires T be non-const-volatile qualified. Use const padded<T> instead of padded<const T>");
  using T::T;                                   // inherit (non-special) constructors
  padded() = default;                           // implement non-inherited special constructors
  /* implicit */ padded(const T& t) : T(t) {}         // cppcheck-suppress noExplicitConstructor          // NOLINT
  /* implicit */ padded(T&& t) : T(std::move(t)) {}   // cppcheck-suppress noExplicitConstructor          // NOLINT
};

} //namespace allocators
} // namespace parlay

#endif // PARLAY_ALLOCATORS_PADDED_H
