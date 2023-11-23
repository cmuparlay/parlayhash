// Example of using upsert
// Inserts with key [0, 2, 4, ..] with value [0, 1, 2, ..]
// Then for all i = [0,1,2,3,...] doubles value if in the table and set to i if not
// Checks table contains [(0,0), (1,1), (2,2), ...]

#include <hash_nogrow/unordered_map.h>

int main() {
  long n = 100000;
  parlay::unordered_map<long, long> map(2*n);
  for (int i = 0; i < n; i++) {
    map.insert(2*i, i);
  }

  // Upsert all values once
  for (int i = 0; i < 2*n; i++) {
    map.upsert(i, [i](std::optional<int> v) -> int {
		    if (v) {
		      return 2 * *v;
		    } else {
		      return i;
		    }
		  });
  }

  for (int i = 0; i < 2*n; i++) {
    auto r =  map.find(i);
    if (!r.has_value() || *r != i) {
      std::cout << "error at: " << i << ": " << r.has_value() << ", " << *r << std::endl;
      abort();
    }
  }
  std::cout << "OK" << std::endl;
}
