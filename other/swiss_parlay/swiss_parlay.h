#ifndef THIRD_PARTY_SWISS_PARLAY_UNORDERED_MAP_H_
#define THIRD_PARTY_SWISS_PARLAY_UNORDERED_MAP_H_

// A highly concurrent, growable, SIMD-accelerated hash map and hash set
// implementation.
//
// This implementation combines the "Swiss Table" layout (pioneered by
// Abseil) with a prior version of "Parlay Hash" which uses
// cooperative-fiber-safe concurrency, sequence-lock based reads,
// fine-grained locking for writes, and epoch-based memory
// reclamation.
//
// === Key Features ===
//
// 1. Swiss Table Layout & SIMD Acceleration
//    - The table is partitioned into "Groups" of 16 slots.
//    - Each group maintains a 16-byte control array (`ctrl`)
//      containing 7-bit hash fingerprints (h2) of the keys, or
//      special markers (empty = 0x80, forwarded = 0xfe).
//    - Google's Highway SIMD library is used to compare a target
//      key's fingerprint against all 16 slots in a group
//      simultaneously using vector instructions.  This eliminates
//      most branch mispredictions during lookups.
//    - For trivially copyable types (or pairs/tuples of such types),
//      all values are stored directly in the group array avoiding any
//      indirection, and also avoiding the need for protection by the
//      epoch-based reclamation scheme.  Other types are stored in the
//      heap via a level of indirection, required to make concurrency
//      safe.  They are never copied or moved.
//
// 2. Concurrency Control
//    - Reads and writes coordinate through a sequence lock on each group.
//    - Reads (Finds) do not take locks. They check a sequence number
//      before and after, and if they detect a concurrent write, they
//      retry.  They are not technically lock-free since they can
//      block if a writer stalls while holding the sequence lock (an
//      odd sequence number), but perform much better than read locks.
//    - Writes (Inserts, Removes, Upserts, and Copying during growth)
//      acquire a fine-grained lock on the target Group. To minimize
//      memory overhead, locks are not stored in the groups
//      themselves; instead, group addresses are mapped to a global
//      striped lock pool.
//
// 3. Overflow Chains for Collision Resolution
//    - If a Group's 16 slots are completely full, collisions are resolved
//      using an atomic overflow linked list attached to the Group.
//    - This greatly simplifies concurrent updates and copying during
//      growth since each group is independent.  It also prevents the
//      "primary clustering" issues of open addressing under high
//      load.
//    - The header for each group therefore consists of 16 control
//      bytes, 8 bytes for the sequence lock, and 8 bytes for the
//      overflow pointer (32 bytes total).
//
// 4. Resizing with minimally blocking (Incremental Growing)
//    - When the table capacity is exceeded, it allocates a new
//      `table_version` with 4x more groups.
//    - Migration is done incrementally.  When growing, any update
//      will copy its group, and some constant number of other groups
//      to the new table version.
//    - Groups that have been copied are marked with a special
//      `kForwarded` control byte.  Any operation (query or update)
//      that encounters a forwarded group automatically redirects to
//      the new table version.
//    - Each initial group gets copied to 4 new groups avoiding any
//      synchronization among the groups.
//    - While an individual group is growing (a reasonably fast
//      operation) other operations are blocked from accessing that
//      group.
//    - New groups are first touched when copied to, avoiding a
//      sequential initialization of the new array of groups.
//
// 5. Cooperative Fiber Safety & Performance
//    - Designed specifically to run safely under cooperative fiber
//      schedulers (like Gloop).
//      - Avoids all block-scope static variables and
//        compiler-generated runtime initialization guards, which
//        trigger deadlocks when fibers yield.
//      - Leverages Epoch-Based Reclamation (`epoch.h`) to safely
//        defer the deletion of retired nodes and table versions until
//        all active readers have exited their epoch.
//
// === Supported Interface ===
//
// This header defines two user-facing concurrent container templates:
// `parlay_unordered_map` and `parlay_unordered_set`. Both are built on top
// of the lock-free/fine-grained locked `swiss_parlay_table` and use epoch-based
// memory reclamation.
//
// -----------------------------------------------------------------------------
// 1. parlay_unordered_map<K, V, Hash = std::hash<K>,
//                         KeyEqual = std::equal_to<K>>
// -----------------------------------------------------------------------------
// A concurrent map. Key-value pairs are stored as `std::pair<K, V>`.
//
// Key Types:
//   - `iterator`: Forward iterator
//
// Public Methods:
//   - `parlay_unordered_map()` / `explicit parlay_unordered_map(size_t n)`
//     Constructs the map. `n` is the expected number of entries.
//
//   - `void clear()`
//     Clears the map (re-allocates the underlying table).
//
//   - `int64_t size() const` / `bool empty() const`
//     Size returns size (O(size) operation), empty returns if empty.
//
//   - `std::optional<V> Find(const K& key)` / `bool contains(const K& key)`
//     Looks up a key. `Find` returns the value if found, `std::nullopt`
//     otherwise. `contains` returns true if key is found.
//
//   - `std::optional<V> Insert(const K& key, const V& value)`
//     Inserts the key-value pair. If the key exists, does NOT overwrite and
//     returns the *existing* value. If inserted, returns `std::nullopt`.
//
//   - `std::pair<iterator, bool> insert(const std::pair<K, V>& val)`
//     STL-like insert. Returns {iterator, inserted_bool}.
//
//   - `std::optional<V> Remove(const K& key)` / `size_t erase(const K& key)`
//     Removes the key. `Remove` returns the removed value if found, or
//     `std::nullopt`. `erase` returns 1 if erased, 0 otherwise.
//
//   - `template <typename F> std::optional<V> Upsert(const K& key, const F& f)`
//     Updates value using `f(old_value)` or inserts `f(std::nullopt)`.
//     `f` must be `V(std::optional<V>)`. Returns old value if updated,
//     `std::nullopt` if inserted.
//
//   - `std::optional<V> Upsert(const K& key, const V& value)`
//     Overwrites or inserts `value`. Returns old value if updated,
//     `std::nullopt` if inserted.
//
//   - `template <typename F> void for_each(const F& f)`
//     Applies `f(std::pair<K, V>)` to all entries in parallel.
//
// -----------------------------------------------------------------------------
// 2. parlay_unordered_set<K, Hash = std::hash<K>, KeyEqual = std::equal_to<K>>
// -----------------------------------------------------------------------------
// A concurrent set.
//
// Public Methods:
//   - `parlay_unordered_set()` / `explicit parlay_unordered_set(size_t n)`
//     Constructs the set.
//
//   - `void clear()`
//     Clears the set.
//
//   - `int64_t size() const` / `bool empty() const`
//
//   - `bool Find(const K& key)` / `bool contains(const K& key)`
//     Returns true if key exists.
//
//   - `bool Insert(const K& key)`
//     Inserts key. Returns `true` if inserted, `false` if already existed.
//
//   - `bool Remove(const K& key)`
//     Removes key. Returns `true` if removed, `false` if not found.
//
//   - `template <typename F> void for_each(const F& f)`
//     Applies `f(K)` to all entries in parallel.

#include <algorithm>
#include <atomic>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <iterator>
#include <limits>
#include <mutex>
#include <new>
#include <optional>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

//#define GOOGLE

#ifdef GOOGLE
#include "third_party/flock/utils/epoch.h"
#include "third_party/highway/hwy/highway.h"
#include "third_party/parlay/include/parlay/delayed.h"
#include "third_party/parlay/include/parlay/parallel.h"
#include "third_party/parlay/include/parlay/primitives.h"
#include "third_party/parlay/include/parlay/sequence.h"
#include "third_party/parlay/include/parlay/thread_specific.h"
#else
#include "utils/epoch.h"
#include "hwy/highway.h"
#include "parlay/delayed.h"
#include "parlay/parallel.h"
#include "parlay/primitives.h"
#include "parlay/sequence.h"
#include "parlay/thread_specific.h"
#endif

// Highway defaults to SVE2 on ARM processors (if available), but NEON is faster
// for what we need.
#if defined(__aarch64__) || defined(__arm__) || defined(_M_ARM64) || defined(_M_ARM)
#define HWY_BASELINE_TARGETS HWY_NEON
#endif

namespace parlay {
// Force sequential initialization of Parlay's thread ID pool to avoid
// deadlocks in fibers.
inline int dummy_parlay_init = (parlay::my_thread_id(), 0);

HWY_BEFORE_NAMESPACE();

#define USE_SET

namespace internal {

extern inline auto& get_locks() {
  static std::atomic<bool> locks[1ul << 14] = {};
  return locks;
}

// The body of the table.  General for both Maps and Sets, and for both
// direct and indirect values, depending on the definitions in
// Entries.   Specialized at the bottom of the file.
template <typename Entries>
struct swiss_parlay_table {

  // A table that is initiallized with size n will have fill_factor *
  // n entries.  Making this smaller saves memory at the cost of
  // performance. Making this larger improves performance at the cost
  // of memory.
  static constexpr float kFillFactor = 1.4;
  static_assert(kFillFactor >= 1, "Fill factor must be at least 1");

  // Fraction of buckets with overflow that sets off a grow step
  static constexpr float kRegrowFraction = .4;

  static constexpr size_t kGrowthFactor = 4;
  static_assert((kGrowthFactor & (kGrowthFactor - 1)) == 0,
                "Growth factor must be a power of 2");
  static_assert(kGrowthFactor > 1, "Growth factor must be greater than 1");

  // must be power of 2, and byte vectors of the given size supported
  // by the architecture.   16 is the standard.
  static constexpr size_t kGroupSize = 16;

  struct Iterator;

  using Policy = typename Entries::Policy;
  // raw entries stored in slots (for indirect, it will be a pointer)
  using slot_type = typename Entries::Entry;
  // type returned by Find, Insert, Delete and Upsert
  // i.e. std::optional<V> for maps and bool for sets
  using result_type = typename Policy::result_type;
  // std::pair<K,V> for maps, and K for sets
  using value_type = typename Policy::value_type; 
  using K = typename Policy::K;
  using Hash = typename Policy::Hash;
  using KeyEqual = typename Policy::KeyEqual;

  // conditionally rehash if type Hash::is_avalanching is not defined
  template <typename H, typename ignore = void>
  struct rehash {
    size_t operator()(size_t h) const {
      size_t x = h * UINT64_C(0xbf58476d1ce4e5b9);  // linear transform
      return (x ^ (x >> 31));                       // non-linear transform
    }
  };

  template <typename H>
  struct rehash<H, typename H::is_avalanching> {
    size_t operator()(size_t i) const { return i; }
  };

  size_t hash(const K& key) const { return rehash<Hash>{}(Hash{}(key)); }
  static size_t fast_map(size_t hash_val, size_t num_groups) {
    if (num_groups < (1ULL << 32)) [[likely]] {
      uint32_t hash_32 = static_cast<uint32_t>(hash_val);
      return (static_cast<uint64_t>(hash_32) * num_groups) >> 32;
    }
    return (static_cast<unsigned __int128>(hash_val) * num_groups) >> 57;
  }

  Entries entries;

  auto try_acquire_lock(uint64_t h) {
    constexpr uint64_t mask = (1ul << 14) - 1;
    uint64_t idx = h & mask;
    bool old = false;
    std::atomic<bool>& lck = get_locks()[idx];
    return (!lck.load() &&
            lck.compare_exchange_strong(old, true,
                                        std::memory_order_acquire,
                                        std::memory_order_relaxed));
  }

  auto release_lock(uint64_t h) {
    constexpr uint64_t mask = (1ul << 14) - 1;
    uint64_t idx = h & mask;
    get_locks()[idx].store(false, std::memory_order_release);
  }

  struct Node {
    slot_type entry;
    std::atomic<Node*> next;
    Node(const slot_type& entry, Node* next) : entry(entry), next(next) {}
  };

  // Holds a group of kGroupSize entries, along with a kGroupSize-byte control block
  // that contains for each entry a 7-bit secondary hash, and a bit to
  // indicate if full/empty.  Contains a sequence number used as a
  // sequence lock.  It is odd if locked and even otherwise.  Every
  // update increments it by two (+1 to lock, +1 to unlock).  Contains
  // an overflow list used if we run out of the kGroupSize primary slots.
  struct alignas(32) Group {
    uint8_t ctrl[kGroupSize];
    std::atomic<uint64_t> seq;
    std::atomic<Node*> overflow;
    slot_type slots[kGroupSize];

    Group() : seq(0), overflow(nullptr) {
      std::fill(std::begin(ctrl), std::end(ctrl), kEmpty);  // all empty
    }
  };

  // Control byte stored in slots that are empty.
  static constexpr uint8_t kEmpty = 0x80;

  // This is stored in the sequence number to indicate that the group
  // is forwarded.  Importantly it is odd, so acts as a locked state.
  static constexpr uint64_t kForwarded = std::numeric_limits<uint64_t>::max();

  struct table_version {
    size_t num_groups;
    // The array of groups
    Group* groups;
    // Updated after a grow cycle
    std::atomic<table_version*> next{nullptr};
    // Used to count the number of overflows in first 100 groups so as
    // to detect when to grow.
    std::atomic<int64_t> overflow_groups_count{0};
    // When copying, indicates how many groups have been copied
    std::atomic<size_t> completed_count{0};
    // When copying, indicates next slot to copy
    std::atomic<size_t> copy_counter{0};
    // Used to lock when allocating memory to copy into
    // NOLINTNEXTLINE(google3-custom-lockable-without-annotations)
    std::mutex allocate_lock;
    epoch::memory_pool<Node>* node_pool;

    explicit table_version(size_t n, epoch::memory_pool<Node>* pool,
                           bool init_groups = false)
        : num_groups(n), node_pool(pool) {
      void* mem = std::aligned_alloc(32, num_groups * sizeof(Group));
      if (mem == nullptr) std::abort();
      groups = reinterpret_cast<Group*>(mem);
      if (init_groups) {
        for (size_t i = 0; i < num_groups; i++) {
          new (&groups[i]) Group();
        }
      }
    }

    // Destructor of table_version does NOT retire slot entries (e.g. freeing
    // heap memory in IndirectEntries) because during resize, active slots are
    // copied to the new version by copying pointers. Only the current_version
    // (the latest table version) owns the entries, which are cleaned up in
    // ~swiss_parlay_table() via retire_all_entries.
    ~table_version() {
      std::free(groups);
    }

    int64_t get_overflow_groups_count() const {
      return overflow_groups_count.load(std::memory_order_relaxed);
    }
  };

  // Used to cache the groups and mask avoiding a level of indirection
  // on the fast path of a find.
  struct alignas(16) groups_and_mask {
    Group* groups;
    size_t num_groups;
  };

  std::atomic<groups_and_mask> cached_groups_and_mask;
  std::atomic<bool> is_growing{false};
  bool clear_memory_at_end;
  std::atomic<table_version*> current_version;
  table_version* initial_version;
  epoch::memory_pool<Node>* node_pool;
  //static_assert(decltype(cached_groups_and_mask)::is_always_lock_free,
  //              "cached_groups_and_mask must be always lock-free");

  groups_and_mask load_cached_info_fast() const {
    return cached_groups_and_mask.load(std::memory_order_acquire);
  }

  explicit swiss_parlay_table(size_t n, bool clear_at_end = false)
      : entries(clear_at_end),
        clear_memory_at_end(clear_at_end),
        node_pool(clear_at_end ? new epoch::memory_pool<Node>()
                               : &epoch::get_default_pool<Node>()) {
    size_t num_groups = std::max<size_t>(1, (kFillFactor * n + kGroupSize - 1) / kGroupSize);
    initial_version = new table_version(num_groups, node_pool, true);
    current_version.store(initial_version);
    cached_groups_and_mask.store(
        {initial_version->groups, initial_version->num_groups});
  }

  // Reclaims all heap allocations stored in the entries of the active table
  // version and clears overflow chains without touching uninitialized groups.
  // Must only be called when the table is being destroyed and no
  // concurrent operations are running.
  void retire_and_clear_group_rec(table_version* tv, size_t g_idx) {
    Group& g = tv->groups[g_idx];
    if (g.seq.load(std::memory_order_relaxed) == kForwarded) {
      table_version* next = tv->next.load(std::memory_order_relaxed);
      if (next != nullptr) {
        for (size_t i = 0; i < kGrowthFactor; ++i) {
          retire_and_clear_group_rec(next, g_idx * kGrowthFactor + i);
        }
      }
    } else {
      for (int j = 0; j < kGroupSize; ++j) {
        if (g.ctrl[j] < kEmpty) {
          entries.retire_entry(g.slots[j]);
        }
      }
      Node* curr = g.overflow.load(std::memory_order_relaxed);
      while (curr != nullptr) {
        Node* next_node = curr->next.load(std::memory_order_relaxed);
        entries.retire_entry(curr->entry);
        tv->node_pool->Delete(curr);
        curr = next_node;
      }
      g.overflow.store(nullptr, std::memory_order_relaxed);
    }
  }

  void retire_all_entries(table_version* tv) {
    for (size_t i = 0; i < tv->num_groups; i++) {
      retire_and_clear_group_rec(tv, i);
    }
  }

  ~swiss_parlay_table() {
    // Clean up heap allocated entries (if using IndirectEntries) from the
    // latest version.
    retire_all_entries(current_version.load());
    // Delete all table versions.
    table_version* curr = initial_version;
    while (curr != nullptr) {
      table_version* next = curr->next.load(std::memory_order_relaxed);
      delete curr;
      curr = next;
    }
    if (clear_memory_at_end) {
      delete node_pool;
    }
  }

  void reset(size_t n) {
    retire_all_entries(current_version.load());
    table_version* curr = initial_version;
    while (curr != nullptr) {
      table_version* next = curr->next.load(std::memory_order_relaxed);
      delete curr;
      curr = next;
    }
    size_t num_groups = std::max<size_t>(1, (kFillFactor * n + kGroupSize - 1) / kGroupSize);
    initial_version = new table_version(num_groups, node_pool, true);
    current_version.store(initial_version);
    cached_groups_and_mask.store(
        {initial_version->groups, initial_version->num_groups});
    is_growing.store(false);
  }

  // Determines number of full entries in a group.  Because of
  // growing, it might need to recurse through copied groups.
  int64_t recursive_group_size(table_version* tv, size_t g_idx) const {
    Group& g = tv->groups[g_idx];
    if (g.seq.load(std::memory_order_acquire) == kForwarded) {
      table_version* next = tv->next.load(std::memory_order_acquire);
      int64_t total_size = 0;
      for (size_t i = 0; i < kGrowthFactor; ++i) {
        total_size += recursive_group_size(next, g_idx * kGrowthFactor + i);
      }
      return total_size;
    } else {
      namespace highway = hwy::HWY_NAMESPACE;
      constexpr highway::FixedTag<uint8_t, kGroupSize> byte_vec;
      auto ctrl_val = highway::Load(byte_vec, g.ctrl);
      auto match_val = highway::Set(byte_vec, kEmpty);  // empty
      auto cmp = highway::Eq(ctrl_val, match_val);
      uint64_t empty_mask = 0;
      highway::StoreMaskBits(byte_vec, cmp,  reinterpret_cast<uint8_t*>(&empty_mask));
      empty_mask &= (1ULL << kGroupSize) - 1;
      int full_slots_count =
          kGroupSize - std::popcount(empty_mask);
      int overflow_count = 0;
      Node* curr = g.overflow.load(std::memory_order_acquire);
      while (curr != nullptr) {
        overflow_count++;
        curr = curr->next.load(std::memory_order_acquire);
      }
      return full_slots_count + overflow_count;
    }
  }

  // We do not keep track of size since that is expensive, so need to
  // go through full table to determine the size.  Safe to call
  // concurrently with updates, but might or might not include any
  // upates that are concurrent with this operation (i.e., it is not
  // strictly linearizable, but has relazed consistency).
  int64_t size() const {
    return epoch::with_epoch([&] {
      table_version* curr = current_version.load(std::memory_order_acquire);
      return parlay::reduce(parlay::delayed::tabulate(curr->num_groups, [&](size_t i) {
        return recursive_group_size(curr, i);
      }));
    });
  }

  // Returns true if sequence lock was successful.
  // Side effects result and target slot if found.
  // Used by Find, Insert, Remove and Upsert.
  bool find_in_group(uint64_t seq1, const K& key,
                     const uint8_t h2, Group* g,
                     result_type& result, int& target_slot) {
    namespace highway = hwy::HWY_NAMESPACE;
    constexpr highway::FixedTag<uint8_t, kGroupSize> byte_vec;
    auto ctrl_val = highway::Load(byte_vec, g->ctrl);
    auto match_val = highway::Set(byte_vec, h2);
    auto cmp = highway::Eq(ctrl_val, match_val);
    uint64_t mask = 0;
    highway::StoreMaskBits(byte_vec, cmp, reinterpret_cast<uint8_t*>(&mask));
    mask &= (1ULL << kGroupSize) - 1;
    // fast path for not found
    Node* overflow_ptr = g->overflow.load(std::memory_order_acquire);
    
    if (mask == 0 && (overflow_ptr == nullptr)) {
      std::atomic_thread_fence(std::memory_order_acquire);
      if (seq1 == g->seq.load(std::memory_order_relaxed)) {
        return true;
      }
    }

    // Returns whether succeeded in either finding or not finding the
    // key (true), or failed because the sequence counter was updated
    // and hence the read was invalid (false).
    // If found then result is side effected to the found value
    auto do_find = [&] {
      slot_type res;
      while (mask > 0) {
        // first search in main slots
        int bit = std::countr_zero(mask);
        slot_type e = g->slots[bit];
        std::atomic_thread_fence(std::memory_order_acquire);
        // need to verify e was read atomically before using it
        if (seq1 == g->seq.load(std::memory_order_relaxed)) [[likely]] {
          if (KeyEqual{}(Entries::get_key(e), key)) [[likely]] {
            result = Entries::get_result(e);
            target_slot = bit;
            return true;
          }
        } else return false;
        mask &= mask - 1;
      }

      // If not found in main slots then search the overflow.
      auto search_overflow = [&] {
        Node* curr = overflow_ptr;
        while (curr != nullptr) {
          if (KeyEqual{}(Entries::get_key(curr->entry), key)) {
            std::atomic_thread_fence(std::memory_order_acquire);
            if (seq1 == g->seq.load(std::memory_order_relaxed)) {
              result = Entries::get_result(curr->entry);
              return true;
            } else {
              return false;
            }
          }
          curr = curr->next.load(std::memory_order_acquire);
        }
        // if here, then key was not found (result has not been side
        // effected).
        std::atomic_thread_fence(std::memory_order_acquire);
        return seq1 == g->seq.load(std::memory_order_relaxed);
      };
      // searching overflow needs to be protected
      if constexpr (Entries::kNeedsEpochProtection) {
        // already protected, no need to protect again
        return search_overflow();
      } else {
        return epoch::with_epoch(search_overflow);
      }
    };

    if constexpr (Entries::kNeedsEpochProtection) {
      if (mask != 0) {
        if constexpr (std::is_pointer_v<typename Entries::Entry>) {
          int bit = std::countr_zero(static_cast<unsigned int>(mask));
          __builtin_prefetch(g->slots[bit]);
        }
      }
      return epoch::with_epoch(do_find);
    } else {
      return do_find();
    }
  }

  result_type Find(const K& key) {
    groups_and_mask gm = load_cached_info_fast();
    size_t h = hash(key);
    size_t g_idx = fast_map(h >> 7, gm.num_groups);
    uint8_t h2 = h & 0x7F;
    Group* g = &(gm.groups[g_idx]);

    while (true) {
      uint64_t seq1 = g->seq.load(std::memory_order_acquire);
      if (seq1 % 2 != 0) [[unlikely]] {
        if (seq1 == kForwarded) {
          // trickiest case is when group is forwaded during growing
          // now cannot use the cached groups and mask.
          table_version* v = current_version.load();
          table_version* new_v = v->next.load(std::memory_order_acquire);
          g_idx = fast_map(h >> 7, v->num_groups);
          g = &v->groups[g_idx];
          seq1 = g->seq.load(std::memory_order_acquire);
          if (seq1 % 2 != 0) {
            if (seq1 == kForwarded && new_v != nullptr) {
              g_idx = fast_map(h >> 7, new_v->num_groups);
              g = &new_v->groups[g_idx];
            }
            continue;
          }
        } else
          continue;  // locked or forwarded, retry
      }

      result_type result{};
      int target_slot = -1; // not used in Find
      if (find_in_group(seq1, key, h2, g, result, target_slot))
        return result;
    }
  }

  void finish_growing(table_version* to) {
    is_growing.store(false);
    current_version.store(to);
    cached_groups_and_mask.store({to->groups, to->num_groups});
  }

  void retire_list(Node* curr) {
    while (curr != nullptr) {
      Node* next = curr->next.load(std::memory_order_relaxed);
      Node* to_delete = curr;
      node_pool->Retire(to_delete);
      curr = next;
    }
  }

  void copy_group(table_version* from, table_version* to, size_t g_idx) {
    Group& g_old = from->groups[g_idx];
    while (true) {
      uint64_t expected = g_old.seq.load(std::memory_order_acquire);
      if (expected == kForwarded) return;
      if (expected % 2 != 0) {
        continue;
      }
      if (g_old.seq.compare_exchange_strong(expected, expected + 1,
                                            std::memory_order_acquire)) {
        // initialize the groups moving to and keep pointers
        Group* target_groups[kGrowthFactor];
        for (size_t i = 0; i < kGrowthFactor; ++i) {
          target_groups[i] = &to->groups[g_idx * kGrowthFactor + i];
          new (target_groups[i]) Group();
        }

        std::vector<slot_type> entries;
        for (int i = 0; i < kGroupSize; ++i) {
          if (g_old.ctrl[i] != kEmpty) {
            entries.push_back(g_old.slots[i]);
          }
        }

        Node* overflow_ptr = g_old.overflow.load(std::memory_order_relaxed);
        Node* curr = overflow_ptr;
        while (curr != nullptr) {
          entries.push_back(curr->entry);
          curr = curr->next.load(std::memory_order_relaxed);
        }

        size_t counters[kGrowthFactor] = {0};

        for (const auto& entry : entries) {
          const K& key = Entries::get_key(entry);
          size_t h = hash(key);
          size_t new_g_idx = fast_map(h >> 7, to->num_groups);
          size_t i = new_g_idx & (kGrowthFactor - 1);

          Group* tg = target_groups[i];
          size_t& cnt = counters[i];
          uint8_t h2 = h & 0x7F;

          if (cnt < kGroupSize) {
            tg->slots[cnt] = entry;
            tg->ctrl[cnt] = h2;
            cnt++;
          } else {
            Node* old_head = tg->overflow.load(std::memory_order_relaxed);
            Node* new_node = node_pool->New(entry, old_head);
            tg->overflow.store(new_node, std::memory_order_relaxed);
            if (old_head == nullptr && new_g_idx < 100) {
              to->overflow_groups_count.fetch_add(1, std::memory_order_relaxed);
            }
          }
        }

        g_old.overflow.store(nullptr, std::memory_order_release);

        retire_list(overflow_ptr);

        size_t finished =
            from->completed_count.fetch_add(1, std::memory_order_acq_rel) + 1;
        if (finished == from->num_groups) {
          finish_growing(to);
        }

        g_old.seq.store(kForwarded, std::memory_order_release);
        return;
      }
    }
  }

  // Incrementally copies some number of groups to next larger table.
  // The copy counter keeps track of which groups and when done.
  void copy_some_groups(table_version* v, table_version* next_v) {
    size_t cnt = std::min<size_t>(8, v->num_groups);
    size_t total_batches = (v->num_groups + cnt - 1) / cnt;
    size_t idx = v->copy_counter.fetch_add(1, std::memory_order_relaxed);
    if (idx < total_batches) {
      size_t start = idx * cnt;
      size_t end = std::min(start + cnt, v->num_groups);
      for (size_t i = start; i < end; i++) copy_group(v, next_v, i);
    }
  }

  void forward_if_needed(size_t h, table_version*& v, size_t& g_idx,
                         Group*& g) {
    auto next_v = v->next.load(std::memory_order_acquire);
    if (next_v != nullptr) {
      copy_group(v, next_v, g_idx);
      copy_some_groups(v, next_v);
      v = v->next.load(std::memory_order_acquire);
      g_idx = fast_map(h >> 7, v->num_groups);
      g = &v->groups[g_idx];
    } else if (v == current_version.load(std::memory_order_acquire) &&
               v->get_overflow_groups_count() >
               std::min<size_t>(v->num_groups, 100) * kRegrowFraction) {
      // if overfull then try to create a new larger table
      std::unique_lock<std::mutex> lck(v->allocate_lock, std::try_to_lock);
      if (!lck.owns_lock() ||
          v->next.load(std::memory_order_acquire) != nullptr)
        return;
      v->next.store(
          new table_version(v->num_groups * kGrowthFactor, node_pool));
      is_growing.store(true);
    }
  }

  result_type Insert(const value_type& entry) {
    groups_and_mask gm = load_cached_info_fast();
    const K& key = Policy::get_k(entry);
    size_t h = hash(key);
    size_t g_idx = fast_map(h >> 7, gm.num_groups);
    uint8_t h2 = h & 0x7F;
    namespace highway = hwy::HWY_NAMESPACE;
    constexpr highway::FixedTag<uint8_t, kGroupSize> byte_vec;
    auto match_val = highway::Set(byte_vec, h2);
    Group* g = &(gm.groups[g_idx]);

    // Fast path for insertion.  If finds key in slots then returns
    // immediately.  If it does not find in slots and not growing, it
    // checks if it can place directly in the primary slots.  Notably
    // improves performance for workloads with high insertion rates.
    if (!is_growing.load(std::memory_order_relaxed)) {
      uint64_t seqn = g->seq.load(std::memory_order_acquire);
      auto ctrl_val = highway::Load(byte_vec, g->ctrl);
      auto cmp = highway::Eq(ctrl_val, match_val);
      uint64_t mask = 0;  // slots where h2 matches
      highway::StoreMaskBits(byte_vec, cmp, reinterpret_cast<uint8_t*>(&mask));
      mask &= (1ULL << kGroupSize) - 1;
      if (mask != 0) {
        int bit = std::countr_zero(mask);
        result_type result{};
        auto check = [&] {
          slot_type e = g->slots[bit];
          std::atomic_thread_fence(std::memory_order_acquire);
          if (((seqn & 1) == 0) &&  // not locked
              g->seq.load(std::memory_order_relaxed) == seqn) { // hasn't changed
            if (KeyEqual{}(Entries::get_key(e), key)) {
              result = Entries::get_result(e);
              return true;
            }
          }
          return false;
        };
        if constexpr (Entries::kNeedsEpochProtection) {
          if (epoch::with_epoch(check)) return result;
        } else {
          if (check()) return result;
        }
      } else {  // no matches in slots
        auto cmp_empty =
            highway::Eq(ctrl_val, highway::Set(byte_vec, kEmpty));
        uint64_t empty_mask = 0;  // slots where h2 is empty
        highway::StoreMaskBits(byte_vec, cmp_empty,
                               reinterpret_cast<uint8_t*>(&empty_mask));
        empty_mask &= (1ULL << kGroupSize) - 1;
        std::atomic_thread_fence(std::memory_order_acquire);
        if (empty_mask != 0 &&    // at least one empty
            ((seqn & 1) == 0)) {  // not locked
          int bit = std::countr_zero(empty_mask);
          slot_type e = entries.make_entry(key, entry);
          if (g->seq.load(std::memory_order_relaxed) == seqn &&  // hasn't changed
              g->seq.compare_exchange_strong(seqn, seqn + 1)) {  // try lock
            std::atomic_thread_fence(std::memory_order_release);
            g->slots[bit] = e;
            g->ctrl[bit] = h2;
            g->seq.store(seqn + 2, std::memory_order_release);
            return {};
          } else entries.retire_entry(e);
        }
      }
    }

    table_version* v = current_version.load(std::memory_order_acquire);
    g_idx = fast_map(h >> 7, v->num_groups);
    g = &(v->groups[g_idx]);

    while (true) {
      forward_if_needed(h, v, g_idx, g);

      uint64_t seq1 = g->seq.load(std::memory_order_acquire);
      if (seq1 % 2 != 0) {
        continue;
      }

      result_type result{};
      int target_slot = -1;
      // Optimistic Pre-check
      if (!find_in_group(seq1, key, h2, g, result, target_slot))
        continue;

      if (Policy::is_found(result)) {
        return result;
      }

      // Now try insert with lock
      auto ctrl_val = highway::Load(byte_vec, g->ctrl);
      auto cmp_empty =
        highway::Eq(ctrl_val, highway::Set(byte_vec, kEmpty));
      uint64_t empty_mask = 0;
      highway::StoreMaskBits(byte_vec, cmp_empty, reinterpret_cast<uint8_t*>(&empty_mask));
      empty_mask &= (1ULL << kGroupSize) - 1;
      slot_type e = entries.make_entry(key, entry);
      uint64_t expected = seq1;
      bool acquired;
      
      if (empty_mask > 0) {
        int bit = std::countr_zero(empty_mask);
        if ((acquired = try_acquire_lock(h)) &&
            g->seq.load(std::memory_order_relaxed) == seq1 &&
            g->seq.compare_exchange_strong(expected, seq1 + 1,
                                           std::memory_order_acquire)) {
          std::atomic_thread_fence(std::memory_order_release);
          g->slots[bit] = e;
          g->ctrl[bit] = h2;
          g->seq.store(seq1 + 2, std::memory_order_release);
          release_lock(h);
          return {};
        }
      } else {
        // Slots full, insert to overflow
        Node* old_head = g->overflow.load(std::memory_order_relaxed);
        Node* new_node =
            node_pool->New(e, old_head);
        if ((acquired = try_acquire_lock(h)) &&
            g->seq.load(std::memory_order_relaxed) == seq1 &&
            g->seq.compare_exchange_strong(expected, seq1 + 1,
                                           std::memory_order_acquire)) {
          g->overflow.store(new_node, std::memory_order_release);
          g->seq.store(seq1 + 2, std::memory_order_release);
          release_lock(h);
          if (old_head == nullptr && g_idx < 100)
            v->overflow_groups_count.fetch_add(1, std::memory_order_relaxed);
          return {};
        } else node_pool->Delete(new_node);
      }
      // if here, then seqlock failed, need to retire entry
      entries.retire_entry(e);
      if (acquired) release_lock(h);
    }
  }

  result_type Remove(const K& key) {
    table_version* v = current_version.load();
    size_t h = hash(key);
    size_t g_idx = fast_map(h >> 7, v->num_groups);
    uint8_t h2 = h & 0x7F;

    Group* g = &(v->groups[g_idx]);

    while (true) {
      forward_if_needed(h, v, g_idx, g);

      uint64_t seq1 = g->seq.load(std::memory_order_acquire);
      if (seq1 % 2 != 0) {
        continue;
      }

      result_type result{};
      int target_slot = -1;
      // Optimistic Pre-check
      if (!find_in_group(seq1, key, h2, g, result, target_slot))
        continue;

      if (!Policy::is_found(result)) {
        return {};
      }

      bool acquired;

      // Lock
      uint64_t expected = seq1;
      if (target_slot != -1) {
        Node* oh = g->overflow.load(std::memory_order_relaxed);
        if (oh != nullptr) {
          Node* next_node = oh->next.load(std::memory_order_relaxed);
          slot_type e;
          if ((acquired = try_acquire_lock(h)) &&
              g->seq.load(std::memory_order_relaxed) == seq1 &&
              g->seq.compare_exchange_strong(expected, seq1 + 1,
                                             std::memory_order_acquire)) {
            std::atomic_thread_fence(std::memory_order_release);
            e = g->slots[target_slot];
            g->slots[target_slot] = oh->entry;
            size_t moved_h = hash(Entries::get_key(oh->entry));
            uint8_t moved_h2 = moved_h & 0x7F;
            g->ctrl[target_slot] = moved_h2;
            g->overflow.store(next_node, std::memory_order_release);
            g->seq.store(seq1 + 2, std::memory_order_release);
            release_lock(h);
            entries.retire_entry(e);
            node_pool->Retire(oh);
            if (next_node == nullptr && g_idx < 100) 
              v->overflow_groups_count.fetch_sub(1, std::memory_order_relaxed);
            return result;
          }
        } else {
          slot_type e;
          if ((acquired = try_acquire_lock(h)) &&
              g->seq.load(std::memory_order_relaxed) == seq1 &&
              g->seq.compare_exchange_strong(expected, seq1 + 1,
                                             std::memory_order_acquire)) {
            std::atomic_thread_fence(std::memory_order_release);
            e = g->slots[target_slot];
            g->ctrl[target_slot] = kEmpty;
            g->seq.store(seq1 + 2, std::memory_order_release);
            release_lock(h);
            entries.retire_entry(e);
            return result;
          }
        }
      } else {
        slot_type e;
        if ((acquired = try_acquire_lock(h)) &&
            g->seq.load(std::memory_order_relaxed) == seq1 &&
            g->seq.compare_exchange_strong(expected, seq1 + 1,
                                           std::memory_order_acquire)) {
          Node* prev = nullptr;
          Node* curr = g->overflow.load(std::memory_order_relaxed);
          while (curr != nullptr) {
            if (KeyEqual{}(Entries::get_key(curr->entry), key)) break;
            prev = curr;
            curr = curr->next.load(std::memory_order_relaxed);
          }

          // curr should not be nullptr since key was found in speculative phase
          Node* next_node = curr->next.load(std::memory_order_relaxed);
          if (prev == nullptr) {
            g->overflow.store(next_node, std::memory_order_release);
            if (next_node == nullptr && g_idx < 100) {
              v->overflow_groups_count.fetch_sub(1, std::memory_order_relaxed);
            }
          } else {
            prev->next.store(next_node, std::memory_order_release);
          }
          e = curr->entry;
          g->seq.store(seq1 + 2, std::memory_order_release);            
          release_lock(h);
          entries.retire_entry(e);
          node_pool->Retire(curr);
          return result;
        }
      }
      if (acquired) release_lock(h);
    }
  }

  template <typename F, typename P = Policy>
  typename std::enable_if_t<P::kIsMap, result_type> upsert(
      const K& key, const F& f) {
    table_version* v = current_version.load();
    size_t h = hash(key);
    size_t g_idx = fast_map(h >> 7, v->num_groups);
    uint8_t h2 = h & 0x7F;

    namespace highway = hwy::HWY_NAMESPACE;
    constexpr highway::FixedTag<uint8_t, kGroupSize> byte_vec;

    Group* g = &(v->groups[g_idx]);

    while (true) {
      forward_if_needed(h, v, g_idx, g);

      uint64_t seq1 = g->seq.load(std::memory_order_acquire);
      if (seq1 % 2 != 0) {
        continue;
      }

      result_type result{};
      int target_slot = -1;
      // Optimistic Pre-check
      if (!find_in_group(seq1, key, h2, g, result, target_slot))
        continue;

      // Lock
      result_type ret_val;
      uint64_t expected = seq1;
      if (g->seq.compare_exchange_strong(expected, seq1 + 1,
                                         std::memory_order_acquire)) {
        if (target_slot != -1) {
          value_type old_val = entries.get_data(g->slots[target_slot]);
          value_type new_val = std::make_pair(key, f(result));
          entries.update_entry(g->slots[target_slot], new_val);
          g->seq.store(seq1 + 2, std::memory_order_release);
          return old_val.second;
        }

        if (Policy::is_found(result)) {
          Node* curr = g->overflow.load(std::memory_order_relaxed);
          while (curr != nullptr) {
            if (KeyEqual{}(Entries::get_key(curr->entry), key)) {
              value_type old_val = entries.get_data(curr->entry);
              value_type new_val = std::make_pair(key, f(result));
              entries.update_entry(curr->entry, new_val);
              ret_val = old_val.second;
              break;
            }
            curr = curr->next.load(std::memory_order_relaxed);
          }
          g->seq.store(seq1 + 2, std::memory_order_release);
          return ret_val;
        }

        // Not found, insert
        auto new_val = f(std::nullopt);
        auto ctrl_val_lock = highway::Load(byte_vec, g->ctrl);
        auto cmp_empty =
            highway::Eq(ctrl_val_lock, highway::Set(byte_vec, kEmpty));
        uint64_t empty_mask = 0;
        highway::StoreMaskBits(byte_vec, cmp_empty, reinterpret_cast<uint8_t*>(&empty_mask));
        empty_mask &= (1ULL << kGroupSize) - 1;
        if (empty_mask > 0) {
          int bit = std::countr_zero(empty_mask);
          g->slots[bit] = entries.make_entry(key, std::make_pair(key, new_val));
          g->ctrl[bit] = h2;
          g->seq.store(seq1 + 2, std::memory_order_release);
          return std::nullopt;
        }

        Node* old_head = g->overflow.load(std::memory_order_relaxed);
        Node* new_node = node_pool->New(
            entries.make_entry(key, std::make_pair(key, new_val)), old_head);
        g->overflow.store(new_node, std::memory_order_release);
        if (old_head == nullptr && g_idx < 100) {
          v->overflow_groups_count.fetch_add(1, std::memory_order_relaxed);
        }
        g->seq.store(seq1 + 2, std::memory_order_release);
        return std::nullopt;
      }
    }
  }


  // Applies f to all elements in group i of t.
  // f must be of type slot_type -> void
  // If the group is forwarded, then include all forwarded entries.
  // Runs sequentially so can be used to gather elements in the group.
  // Not safe with concurrent updates
  template <typename F>
  static void for_each_in_group_rec(table_version* t, int64_t i, const F& f) {
    Group& g = t->groups[i];
    uint64_t seq = g.seq.load(std::memory_order_acquire);
    if (seq != kForwarded) {
      for (int j = 0; j < kGroupSize; j++) {
        if (g.ctrl[j] != kEmpty) {
          f(g.slots[j]);
        }
      }
      Node* curr = g.overflow.load(std::memory_order_acquire);
      while (curr != nullptr) {
        f(curr->entry);
        curr = curr->next.load(std::memory_order_acquire);
      }
    } else {
      table_version* next = t->next.load(std::memory_order_acquire);
      if (next != nullptr) {
        for (size_t j = 0; j < kGrowthFactor; j++) {
          for_each_in_group_rec(next, i * kGrowthFactor + j, f);
        }
      }
    }
  }

  // applies f to every entry in the table
  // f must be of type value_type -> void
  template <typename F>
  void for_each(const F& f) {
    auto g = [&](const slot_type& e) { f(Entries::get_data(e)); };
    table_version* v = current_version.load();
    parlay::parallel_for(0, static_cast<int64_t>(v->num_groups),
                         [&](int64_t i) { for_each_in_group_rec(v, i, g); });
  }

  // return all entries in a group as a vector.  If group is forwarded
  // will recursively gather entries.  Not safe with concurrent
  // updates.
  static std::vector<slot_type> group_entries(table_version* t, int64_t i) {
    std::vector<slot_type> result;
    auto g = [&](const slot_type& e) { result.push_back(e); };
    for_each_in_group_rec(t, i, g);
    return result;
  }

  // returns all the entries in the hash table as value types
  parlay::sequence<value_type> to_sequence() {
    table_version* t = current_version.load();
    return parlay::flatten(parlay::tabulate(t->num_groups,
                                            [&] (int64_t i) {
                                              std::vector<value_type> result;
                                              auto g = [&](const slot_type& e) {
                                                result.push_back(Entries::get_data(e)); };
                                              for_each_in_group_rec(t, i, g);
                                              return result;
                                            }));
  }
    
  // --- Iterator Support ---
  struct Iterator {
   public:
    using value_type = typename Entries::Data;
    using iterator_category = std::forward_iterator_tag;
    using pointer = value_type*;
    using reference = value_type&;
    using difference_type = int64_t;

   private:
    std::vector<slot_type> entries;
    int i;
    table_version* t;
    int64_t group_num;
    bool single;
    bool end;
    slot_type entry;

    void get_next_group() {
      auto g = [&](const slot_type& e) { entries.push_back(e); };
      while (entries.size() == 0 && ++group_num < t->num_groups)
        for_each_in_group_rec(t, group_num, g);
      if (group_num == t->num_groups) end = true;
    }

   public:
    explicit Iterator(bool end)
        : i(0), group_num(-2l), single(false), end(true) {}
    explicit Iterator(table_version* t)
        : t(t), i(0), group_num(-1l), single(false), end(false) {
      get_next_group();
    }
    explicit Iterator(slot_type entry)
        : entry(entry), single(true), end(false) {}

    Iterator& operator++() {
      if (single) {
        end = true;
      } else if (++i == entries.size()) {
        i = 0;
        entries.clear();
        get_next_group();
      }
      return *this;
    }

    Iterator& operator++(int) {
      Iterator tmp = *this;
      operator++();
      return tmp;
    }

    const value_type& operator*() const {
      if (single) return Entries::get_data(entry);
      return Entries::get_data(entries[i]);
    }

    const value_type* operator->() const {
      if (single) return &Entries::get_data(entry);
      return &Entries::get_data(entries[i]);
    }

    bool operator!=(const Iterator& iterator) const {
      return !(end ? iterator.end
                   : (group_num == iterator.group_num && i == iterator.i));
    }
    bool operator==(const Iterator& iterator) const {
      return !(*this != iterator);
    }
  };

  Iterator begin() { return Iterator(current_version.load()); }
  Iterator end() { return Iterator(true); }

};
// ***************************************
// End of definition of swiss_parlay_table
// ***************************************
  
// MapPolicy and SetPolicy are used so we can share the same code for
// implementing maps and sets.  For maps the value_type is a key-value
// pair, but for sets it is just the key.
template <typename K_, typename V_, class Hash_ = std::hash<K_>,
          class KeyEqual_ = std::equal_to<K_>>
struct MapPolicy {
  using K = K_;
  using result_type = std::optional<V_>;
  using Hash = Hash_;
  using KeyEqual = KeyEqual_;
  using value_type = std::pair<K, V_>;
  static const K& get_k(const value_type& x) { return x.first; }
  static result_type get_v(const value_type& x) { return x.second; }
  static bool is_found(const result_type& r) {return r.has_value();}
  static constexpr bool kIsMap = true;
};

template <typename K_, class Hash_ = std::hash<K_>,
          class KeyEqual_ = std::equal_to<K_>>
struct SetPolicy {
  using K = K_;
  using result_type = bool;
  using Hash = Hash_;
  using KeyEqual = KeyEqual_;
  using value_type = K;
  static const K& get_k(const value_type& x) { return x; }
  static result_type get_v(const value_type& x) { return true; }
  static bool is_found(const result_type& r) {return r;}
  static constexpr bool kIsMap = false;
};

// A type is effectively trivially copyable if it can be safely copied
// concurrently without risking crashes from torn reads. Standard
// std::is_trivially_copyable may return false for std::pair or
// std::tuple of trivially copyable types depending on the compiler,
// so we specialize it here.
template <typename T>
struct is_effectively_trivially_copyable : std::is_trivially_copyable<T> {};

template <typename T1, typename T2>
struct is_effectively_trivially_copyable<std::pair<T1, T2>>
    : std::bool_constant<is_effectively_trivially_copyable<T1>::value &&
                         is_effectively_trivially_copyable<T2>::value> {};

template <typename... Args>
struct is_effectively_trivially_copyable<std::tuple<Args...>>
    : std::bool_constant<(is_effectively_trivially_copyable<Args>::value &&
                          ...)> {};

template <typename T>
inline constexpr bool is_effectively_trivially_copyable_v =
    is_effectively_trivially_copyable<T>::value;

template <typename T>
struct is_relocatable : is_effectively_trivially_copyable<T> {};

template <typename T1, typename T2>
struct is_relocatable<std::pair<T1, T2>>
    : std::bool_constant<is_relocatable<T1>::value &&
                         is_relocatable<T2>::value> {};

template <typename... Args>
struct is_relocatable<std::tuple<Args...>>
    : std::bool_constant<(is_relocatable<Args>::value &&
                          ...)> {};

}  // namespace internal

template <typename T, typename Allocator, bool EnableSSO>
class sequence;

namespace internal {

template <typename T, typename Allocator, bool EnableSSO>
struct is_relocatable<parlay::sequence<T, Allocator, EnableSSO>>
    : is_relocatable<T> {};

template <typename T>
inline constexpr bool is_relocatable_v =
    is_relocatable<T>::value;

// DirectEntries stores the value directly in the table slots.
// Safe for types that are effectively trivially copyable because torn reads
// are detected and discarded by sequence number validation without crashing.
template <typename Policy_>
struct DirectEntries {
  using Policy = Policy_;
  using Data = typename Policy::value_type;
  using Entry = Data;
  using K = typename Policy::K;

  static constexpr bool kNeedsEpochProtection = false;

  static const Data& get_data(const Entry& e) { return e; }
  static const K& get_key(const Entry& e) { return Policy::get_k(e); }
  static typename Policy::result_type
  get_result(const Entry& e) { return Policy::get_v(e); }

  explicit DirectEntries(bool clear_at_end = false) {}
  Entry make_entry(const K& k, const Data& d) { return d; }
  void retire_entry(Entry& e) {}
  void update_entry(Entry& slot, const Data& new_data) { slot = new_data; }
};

// IndirectEntries stores pointers to heap-allocated values.
// Necessary for non-trivially copyable types (e.g. std::string) to avoid
// crashing the reader if a torn pointer is dereferenced during a concurrent
// update.
template <typename Policy_>
struct IndirectEntries {
  using Policy = Policy_;
  using Data = typename Policy::value_type;
  using Entry = Data*;
  using K = typename Policy::K;

  static constexpr bool kNeedsEpochProtection = true;

  static const Data& get_data(const Entry& e) { return *e; }
  static const K& get_key(const Entry& e) { return Policy::get_k(*e); }
  static typename Policy::result_type
  get_result(const Entry& e) { return Policy::get_v(*e); }
  bool clear_at_end;
  epoch::memory_pool<Data>* data_pool;

  explicit IndirectEntries(bool clear_at_end = false)
      : clear_at_end(clear_at_end),
        data_pool(clear_at_end ? new epoch::memory_pool<Data>()
                               : &epoch::get_default_pool<Data>()) {}
  ~IndirectEntries() {
    if (clear_at_end) {
      delete data_pool;
    }
  }

  Entry make_entry(const K& k, const Data& d) { return data_pool->New(d); }
  void retire_entry(Entry& e) { data_pool->Retire(e); }
  void update_entry(Entry& slot, const Data& new_data) {
    Entry new_entry = data_pool->New(new_data);
    Entry old = slot;
    slot = new_entry;
    data_pool->Retire(old);
  }
};

// RelocatableEntries stores values as byte arrays and can be used for
// relocatable types (i.e., types that can be moved using memcpy).
template <typename Policy_>
struct RelocatableEntries {
  using Policy = Policy_;
  using Data = typename Policy::value_type;
  using K = typename Policy::K;

  static constexpr bool kNeedsEpochProtection =
      !is_effectively_trivially_copyable_v<Data>;

  bool clear_at_end;
  epoch::memory_pool<Data>* data_pool;

  // Ensure every Entry slot satisfies the natural alignment of Data
  struct alignas(alignof(Data)) Entry {
    char bytes[sizeof(Data)];
  };

  static const Data& get_data(const Entry& e) {
    return *reinterpret_cast<const Data*>(&e);
  }
  static const K& get_key(const Entry& e) {
    return Policy::get_k(get_data(e));
  }
  static typename Policy::result_type get_result(const Entry& e) {
    return Policy::get_v(get_data(e));
  }

  explicit RelocatableEntries(bool clear_at_end = false)
      : clear_at_end(clear_at_end),
        data_pool(clear_at_end ? new epoch::memory_pool<Data>()
                               : &epoch::get_default_pool<Data>()) {}
  ~RelocatableEntries() {
    if (clear_at_end) {
      delete data_pool;
    }
  }

  Entry make_entry(const K& k, const Data& d) {
    Entry e;
    if constexpr (is_effectively_trivially_copyable_v<Data>) {
      std::memcpy(&e, &d, sizeof(Data));
    } else {
      new (&e) Data(d);
    }
    return e;
  }
  void retire_entry(Entry& e) {
    if constexpr (!std::is_trivially_destructible_v<Data>) {
      auto mut_ptr = reinterpret_cast<Data*>(&e);
      Data* p = data_pool->New(std::move(*mut_ptr));
      data_pool->Retire(p);
    }
  }
  void update_entry(Entry& slot, const Data& new_data) {
    if constexpr (is_effectively_trivially_copyable_v<Data>) {
      std::memcpy(&slot, &new_data, sizeof(Data));
    } else {
      retire_entry(slot);
      new (&slot) Data(new_data);
    }
  }
};

}  // end namespace internal

// ***************************************
// The following is the public definition of parlay_unordered_map and
// parlay_unordered_set.
// ***************************************

template <typename K, typename V, class Hash = std::hash<K>,
          class KeyEqual = std::equal_to<K>>
struct parlay_unordered_map {
  using Policy = internal::MapPolicy<K, V, Hash, KeyEqual>;
  using Entries =
      std::conditional_t<internal::is_effectively_trivially_copyable_v<typename Policy::value_type>,
                         internal::RelocatableEntries<Policy>,
                         std::conditional_t<internal::is_relocatable_v<typename Policy::value_type>,
                                            internal::RelocatableEntries<Policy>,
                                            internal::IndirectEntries<Policy>>>;
  using Table = internal::swiss_parlay_table<Entries>;
  Table table;
  size_t initial_size;

  // For benchmark compatibility
  using K_ = K;
  using V_ = V;

  parlay_unordered_map() : parlay_unordered_map(1000) {}
  explicit parlay_unordered_map(size_t n, bool clear_memory_at_end = false)
      : table(n, clear_memory_at_end), initial_size(n) {}

  void clear() { table.reset(initial_size); }

  int64_t size() const { return table.size(); }

  bool empty() const { return size() == 0; }
  bool contains(const K& key) { return Find(key).has_value(); }
  int64_t count(const K& key) { return contains(key) ? 1 : 0; }

  using iterator = typename Table::Iterator;
  iterator begin() { return table.begin(); }
  iterator end() { return table.end(); }

  std::optional<V> Find(const K& key) { return table.Find(key); }

  std::optional<V> Insert(const K& key, const V& value) {
    return table.Insert(std::make_pair(key, value));
  }

  std::optional<V> Remove(const K& key) { return table.Remove(key); }

  size_t erase(const K& key) { return Remove(key).has_value() ? 1 : 0; }

  template <typename F>
  std::optional<V> Upsert(const K& key, const F& f) {
    return table.upsert(key, f);
  }

  std::optional<V> Upsert(const K& key, const V& value) {
    auto f = [&](std::optional<V> old) { return value; };
    return table.upsert(key, f);
  }

  template <typename F>
  bool upsert(const K& key, const F& f) {
    Upsert(key, f);
    return true;
  }

  template <typename F>
  void for_each(const F& f) { table.for_each(f); }

  parlay::sequence<std::pair<K,V>> to_sequence() {
    return table.to_sequence(); }
};

template <typename K, class Hash = std::hash<K>,
          class KeyEqual = std::equal_to<K>>
struct parlay_unordered_set {
  using Policy = internal::SetPolicy<K, Hash, KeyEqual>;
  using Entries =
    std::conditional_t<internal::is_effectively_trivially_copyable_v<typename Policy::value_type>,
                       internal::RelocatableEntries<Policy>,
                       std::conditional_t<internal::is_relocatable_v<typename Policy::value_type>,
                                          internal::RelocatableEntries<Policy>,
                                          internal::IndirectEntries<Policy>>>;
  using Table = internal::swiss_parlay_table<Entries>;
  Table table;
  size_t initial_size;

  parlay_unordered_set() : parlay_unordered_set(1000) {}
  explicit parlay_unordered_set(size_t n, bool clear_memory_at_end = false)
      : table(n, clear_memory_at_end), initial_size(n) {}

  void clear() { table.reset(initial_size); }

  int64_t size() const { return table.size(); }

  bool empty() const { return size() == 0; }
  bool contains(const K& key) { return Find(key); }
  int64_t count(const K& key) { return contains(key) ? 1 : 0; }

  using iterator = typename Table::Iterator;
  iterator begin() { return table.begin(); }
  iterator end() { return table.end(); }

  bool Find(const K& key) { return table.Find(key); }

  bool Insert(const K& key) { return !table.Insert(key); }

  bool Remove(const K& key) { return table.Remove(key); }

  template <typename F>
  void for_each(const F& f) {
    table.for_each(f);
  }

  parlay::sequence<K> to_sequence() {
    return table.to_sequence(); }
};

}  // namespace parlay

HWY_AFTER_NAMESPACE();

#endif  // THIRD_PARTY_SWISS_PARLAY_UNORDERED_MAP_H_
