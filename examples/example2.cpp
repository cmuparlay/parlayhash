#include <hash_nogrow/unordered_map.h>

#define NUM_ITERS 1000

int main() {
    parlay::unordered_map<long, long> map(NUM_ITERS);
    for (int i = 0; i < NUM_ITERS; i++) {
        map.insert(i, i);
    }

    // Upsert all values once
    for (int i = 0; i < NUM_ITERS; i++) {
        map.upsert(i, [i](std::optional<int> v) -> int {
            if (v) {
                return 2 * i;
            } else {
                return -i;
            }
        });
    }
}
