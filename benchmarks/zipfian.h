#include <cmath>
#include <cstdint>
#include <random>

#include "parlay/primitives.h"
#include "parlay/delayed.h"
#include "parlay/random.h"

// A generator for the zipfian distribution.
// When constructed with z = zipfian(n, theta) the distribution will
// include values up to n, and with zipfian parameter theta
// Theta must be in the range [0,1)
// Applying z(i) will return the i-th sample from the distribution
struct zipfian {
private:

  parlay::random_generator gen;
  std::uniform_real_distribution<double> dis;
  uint64_t items;
  double theta, zeta_n, eta, alpha;

  double Zeta(uint64_t n) {
    return parlay::reduce(parlay::delayed_tabulate(n, [=] (uint64_t i) {
	  return 1.0/ std::pow(i+1, theta);}));
  }

public:
  zipfian(uint64_t items, double theta)
    : items(items), theta(theta),
      gen(parlay::random_generator(0)),
      dis(std::uniform_real_distribution(0.0,1.0))
  {
    double zeta_2 = Zeta(2);
    zeta_n = Zeta(items);
    alpha = 1.0 / (1.0 - theta);
    eta = (1 - std::pow(2.0 / items, 1 - theta)) / (1 - zeta_2 / zeta_n);
  }

  uint64_t operator () (uint64_t i) {
    auto r = gen[i];
    double u = dis(r);   // a number between 0 and 1
    double uz = u * zeta_n;
    if (uz < 1.0) return 0;
    if (uz < 1.0 + std::pow(0.5, theta)) return 1;
    return std::lround((items-1) * std::pow(eta * u - eta + 1, alpha));
  }

};
