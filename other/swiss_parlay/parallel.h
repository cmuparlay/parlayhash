#ifndef THIRD_PARTY_FLOCK_UTILS_PARALLEL_H_
#define THIRD_PARTY_FLOCK_UTILS_PARALLEL_H_

#ifdef USE_PARLAY

#include "parlay/delayed.h"
#include "parlay/primitives.h"
#include "parlay/scheduler.h"
#include "parlay/sequence.h"  

namespace parlay {
#define PARLAY_USE_STD_ALLOC 1

struct scheduler_type {
  scheduler_pointer ptr;
  scheduler_type(int num_workers) : ptr(initialize_scheduler(num_workers)) {}
};

template <typename F>
long tabulate_reduce(long n, const F& f) {
  return parlay::reduce(
      parlay::delayed::tabulate(n, [&](size_t i) { return f(i); }));
}

template <typename F>
void parallel_for(long n, const F& f) {
  parlay::parallel_for(0, n, [&](long i) { f(i); });
}

}  // namespace parlay
#else
namespace parlay {

struct scheduler_type {
  explicit scheduler_type(int num_procs) {}
};

template <typename F>
long tabulate_reduce(long n, const F& f) {
  long r = 0;
  for (long i = 0; i < n; i++) r += f(i);
  return r;
}

template <typename F>
void parallel_for(long n, const F& f) {
  for (long i = 0; i < n; i++) f(i);
}
}  // namespace parlay
#endif

#endif  // THIRD_PARTY_FLOCK_UTILS_PARALLEL_H_
