#include <parlay/internal/concurrency/big_atomic.h>

namespace parlay {
  template <typename T>
  using atomic = big_atomic<T>;
} 

