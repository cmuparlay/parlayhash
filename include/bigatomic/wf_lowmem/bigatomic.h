#include <parlay/internal/concurrency/big_atomic2.h>

namespace parlay {
  template <typename T>
  using atomic = big_atomic<T>;
} 

