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
//      - Uses `absl::NoDestructor` to avoid exit-time destruction
//        order issues for global metadata.
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
#include <functional>
#include <iterator>
#include <limits>
#include <memory>
#include <new>
#include <optional>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

#include "absl/synchronization/mutex.h"
#include "hwy/highway.h"
#include <parlay/thread_specific.h>
#include <utils/epoch.h>
#include "parallel.h"
// #include "third_party/absl/synchronization/mutex.h"
// #include "third_party/flock/utils/epoch.h"
// #include "third_party/flock/utils/parallel.h"
// #include "third_party/highway/hwy/highway.h"
// #include "third_party/parlay/include/parlay/thread_specific.h"

namespace parlay {
// Force sequential initialization of Parlay's thread ID pool to avoid
// deadlocks in fibers.
inline int dummy_parlay_init = (parlay::my_thread_id(), 0);

HWY_BEFORE_NAMESPACE();

#define USE_SET

namespace internal {
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

// DirectEntries stores the value directly in the table slots.
// Safe for types that are effectively trivially copyable because torn reads
// are detected and discarded by sequence number validation without crashing.
template <typename Policy_>
struct DirectEntries {
  using Policy = Policy_;
  using Data = typename Policy::value_type;
  using Entry = Data;
  using K = typename Policy::K;

  static const Data& get_data(const Entry& e) { return e; }
  static const K& get_key(const Entry& e) { return Policy::get_k(e); }
  static const typename Policy::result_type
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

  static const Data& get_data(const Entry& e) { return *e; }
  static const K& get_key(const Entry& e) { return Policy::get_k(*e); }
  static const typename Policy::result_type
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

// The body of the table
template <typename Entries>
struct swiss_parlay_table {
  // A table that is initiallized with size n will have fill_factor *
  // n entries and then rounded up to the next power of 2.
  // Making this smaller saves memory at the cost of performance
  // Making this larger improves performance at the cost of memory
  static constexpr float kFillFactor = 1.5;
  static_assert(kFillFactor >= 1, "Fill factor must be at least 1");

  // Fraction of buckets with overflow that sets off a grow step
  static constexpr float kRegrowFraction = .2;

  static constexpr size_t kGrowthFactor = 4;
  static_assert((kGrowthFactor & (kGrowthFactor - 1)) == 0,
                "Growth factor must be a power of 2");
  static_assert(kGrowthFactor > 1, "Growth factor must be greater than 1");

  struct Iterator;

  using Policy = typename Entries::Policy;
  using K = typename Policy::K;
  using result_type = typename Policy::result_type;
  using value_type = typename Policy::value_type;
  using Hash = typename Policy::Hash;
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
  static inline size_t fast_map(size_t hash_val, size_t num_groups) {
    if (num_groups < (1ULL << 32)) [[likely]] {
      uint32_t hash_32 = static_cast<uint32_t>(hash_val);
      return (static_cast<uint64_t>(hash_32) * num_groups) >> 32;
    }
    return (static_cast<unsigned __int128>(hash_val) * num_groups) >> 57;
  }
  using KeyEqual = typename Policy::KeyEqual;
  using slot_type = typename Entries::Entry;

  Entries entries;

  struct Node {
    slot_type entry;
    std::atomic<Node*> next;
    Node(const slot_type& entry, Node* next) : entry(entry), next(next) {}
  };

  // Holds a group of 16 entries, along with a 16-byte control block
  // that contains for each entry a 7-bit secondary hash, and a bit to
  // indicate if full/empty.  Contains a sequence number used as a
  // sequence lock.  It is odd if locked and even otherwise.  Every
  // update increments it by two (+1 to lock, +1 to unlock).  Contains
  // an overflow list used if we run out of the 16 primary slots.
  struct alignas(32) Group {
    uint8_t ctrl[16];
    std::atomic<uint64_t> seq;
    std::atomic<Node*> overflow;
    slot_type slots[16];

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
      for (size_t i = 0; i < num_groups; i++) {
        Group& g = groups[i];
        Node* curr = g.overflow.load(std::memory_order_relaxed);
        while (curr != nullptr) {
          Node* next_node = curr->next.load(std::memory_order_relaxed);
          node_pool->Delete(curr);
          curr = next_node;
        }
      }

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
  // static_assert(decltype(cached_groups_and_mask)::is_always_lock_free,
  //              "cached_groups_and_mask must be always lock-free");

  groups_and_mask load_cached_info_fast() const {
    return cached_groups_and_mask.load(std::memory_order_acquire);
  }

  explicit swiss_parlay_table(size_t n, bool clear_at_end = false)
      : entries(clear_at_end),
        clear_memory_at_end(clear_at_end),
        node_pool(clear_at_end ? new epoch::memory_pool<Node>()
                               : &epoch::get_default_pool<Node>()) {
    size_t num_groups = std::max<size_t>(1, (kFillFactor * n + 15) / 16);
    initial_version = new table_version(num_groups, node_pool, true);
    current_version.store(initial_version);
    cached_groups_and_mask.store(
        {initial_version->groups, initial_version->num_groups});
  }

  // Reclaims all heap allocations stored in the entries of the active table
  // version. Must only be called when the table is being destroyed and no
  // concurrent operations are running.
  void retire_all_entries(table_version* tv) {
    for (size_t i = 0; i < tv->num_groups; i++) {
      Group& g = tv->groups[i];
      for (int j = 0; j < 16; ++j) {
        if (g.ctrl[j] < kEmpty) {
          entries.retire_entry(g.slots[j]);
        }
      }
      Node* curr = g.overflow.load(std::memory_order_relaxed);
      while (curr != nullptr) {
        entries.retire_entry(curr->entry);
        curr = curr->next.load(std::memory_order_relaxed);
      }
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
      constexpr highway::FixedTag<uint8_t, 16> byte_vec_16;
      auto ctrl_val = highway::Load(byte_vec_16, g.ctrl);
      auto match_val = highway::Set(byte_vec_16, kEmpty);  // empty
      auto cmp = highway::Eq(ctrl_val, match_val);
      uint16_t empty_mask = 0;
      highway::StoreMaskBits(byte_vec_16, cmp,  reinterpret_cast<uint8_t*>(&empty_mask));
      int full_slots_count =
          16 - std::popcount(static_cast<unsigned int>(empty_mask));
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
      return parlay::tabulate_reduce(curr->num_groups, [&](size_t i) {
        return recursive_group_size(curr, i);
      });
    });
  }

  // returns true if sequence lock was successful
  // side effects result and target slot
  bool find_in_group(uint64_t seq1, const K& key,
                     const uint8_t h2, Group* g,
                     result_type& result, int& target_slot) {
    namespace highway = hwy::HWY_NAMESPACE;
    constexpr highway::FixedTag<uint8_t, 16> byte_vec_16;
    auto ctrl_val = highway::Load(byte_vec_16, g->ctrl);
    auto match_val = highway::Set(byte_vec_16, h2);
    auto cmp = highway::Eq(ctrl_val, match_val);
    uint16_t mask = 0;
    highway::StoreMaskBits(byte_vec_16, cmp, reinterpret_cast<uint8_t*>(&mask));
    if (mask == 0 &&
        g->overflow.load(std::memory_order_acquire) == nullptr) {
      std::atomic_thread_fence(std::memory_order_acquire);
      if (seq1 == g->seq.load(std::memory_order_relaxed)) {
        return true;
      }
    }

    auto do_find = [&] {
      slot_type res;
      bool found = false;
      while (mask > 0) {
        int bit = std::countr_zero(static_cast<unsigned int>(mask));
        if (KeyEqual{}(Entries::get_key(g->slots[bit]), key)) [[likely]] {
          res = g->slots[bit];
          found = true;
          target_slot = bit;
          break;
        }
        mask &= mask - 1;
      }

      if (!found &&
          g->overflow.load(std::memory_order_acquire) != nullptr) {
        auto search_overflow = [&] {
          Node* curr = g->overflow.load(std::memory_order_acquire);
          while (curr != nullptr) {
            if (KeyEqual{}(Entries::get_key(curr->entry), key)) {
              res = curr->entry;
              found = true;
              break;
            }
            curr = curr->next.load(std::memory_order_acquire);
          }
        };
        if constexpr (std::is_pointer_v<typename Entries::Entry>) {
          search_overflow();
        } else {
          epoch::with_epoch(search_overflow);
        }
      }

      std::atomic_thread_fence(std::memory_order_acquire);
      if (seq1 == g->seq.load(std::memory_order_relaxed)) {
        if (found)
          result = Entries::get_result(res);
        return true;
      }
      return false;
    };

    if constexpr (std::is_pointer_v<typename Entries::Entry>) {
      if (mask != 0) {
        int bit = std::countr_zero(static_cast<unsigned int>(mask));
        __builtin_prefetch(g->slots[bit]);
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

  Iterator find_iterator(const K& key) {
    groups_and_mask gm = load_cached_info_fast();
    namespace highway = hwy::HWY_NAMESPACE;
    constexpr highway::FixedTag<uint8_t, 16> byte_vec_16;
    size_t h = hash(key);
    uint8_t h2 = h & 0x7F;
    auto match_val = highway::Set(byte_vec_16, h2);

    size_t g_idx = fast_map(h >> 7, gm.num_groups);
    Group* g = &(gm.groups[g_idx]);

    while (true) {
      uint64_t seq1 = g->seq.load(std::memory_order_acquire);
      if (seq1 % 2 != 0) [[unlikely]] {
        if (seq1 == kForwarded) [[unlikely]] {
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
          continue;
      }

      auto ctrl_val = highway::Load(byte_vec_16, g->ctrl);
      auto cmp = highway::Eq(ctrl_val, match_val);
      uint16_t mask_bits = 0;
      highway::StoreMaskBits(byte_vec_16, cmp, reinterpret_cast<uint8_t*>(&mask_bits));
      if (mask_bits == 0 &&
          g->overflow.load(std::memory_order_acquire) == nullptr) {
        std::atomic_thread_fence(std::memory_order_acquire);
        if (g->seq.load(std::memory_order_relaxed) == seq1) {
          return end();
        }
        continue;
      }

      Iterator res = end();
      bool found = false;

      auto do_compare = [&] {
        uint16_t active_mask = mask_bits;
        while (active_mask > 0) {
          int bit = std::countr_zero(static_cast<unsigned int>(active_mask));
          if (KeyEqual{}(Entries::get_key(g->slots[bit]), key)) [[likely]] {
            res = Iterator(g->slots[bit]);
            found = true;
            break;
          }
          active_mask &= active_mask - 1;
        }

        if (!found && g->overflow.load(std::memory_order_acquire) != nullptr) {
          auto search_overflow = [&] {
            Node* curr = g->overflow.load(std::memory_order_acquire);
            while (curr != nullptr) {
              if (KeyEqual{}(Entries::get_key(curr->entry), key)) {
                res = Iterator(curr->entry);
                found = true;
                break;
              }
              curr = curr->next.load(std::memory_order_acquire);
            }
          };
          if constexpr (std::is_pointer_v<typename Entries::Entry>) {
            search_overflow();
          } else {
            epoch::with_epoch(search_overflow);
          }
        }
      };

      if constexpr (std::is_pointer_v<typename Entries::Entry>) {
        epoch::with_epoch(do_compare);
      } else {
        do_compare();
      }

      std::atomic_thread_fence(std::memory_order_acquire);
      if (g->seq.load(std::memory_order_relaxed) == seq1) {
        return res;
      }
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
        for (int i = 0; i < 16; ++i) {
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

          if (cnt < 16) {
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
      std::lock_guard<std::mutex> lck(v->allocate_lock);
      if (v->next.load(std::memory_order_acquire) != nullptr) return;
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
    constexpr highway::FixedTag<uint8_t, 16> byte_vec_16;
    auto match_val = highway::Set(byte_vec_16, h2);
    Group* g = &(gm.groups[g_idx]);

    // Fast path for insertion.  If finds key in slots then returns
    // immediately.  If it does not find in slots and not growing, it
    // checks if it can place directly in the primary slots.  Notably
    // improves performance for workloads with high insertion rates.
    if (!is_growing.load(std::memory_order_relaxed)) {
      uint64_t seqn = g->seq.load(std::memory_order_acquire);
      auto ctrl_val = highway::Load(byte_vec_16, g->ctrl);
      auto cmp = highway::Eq(ctrl_val, match_val);
      uint16_t mask = 0;  // slots where h2 matches
      highway::StoreMaskBits(byte_vec_16, cmp, reinterpret_cast<uint8_t*>(&mask));
      if (mask != 0) {
        int bit = std::countr_zero(static_cast<unsigned int>(mask));
        result_type result{};
        auto check = [&] {
          if (KeyEqual{}(Entries::get_key(g->slots[bit]), key)) {
            auto r = g->slots[bit];
            std::atomic_thread_fence(std::memory_order_acquire);
            if (((seqn & 1) == 0) &&  // not locked
                g->seq.load(std::memory_order_relaxed) == seqn) { // hasn't changed
              result = Entries::get_result(r);
              return true;
            }
          }
          return false;
        };
        if constexpr (std::is_pointer_v<typename Entries::Entry>) {
          if (epoch::with_epoch(check)) return result;
        } else {
          if (check()) return result;
        }
      } else {  // no matches in slots
        auto cmp_empty =
            highway::Eq(ctrl_val, highway::Set(byte_vec_16, kEmpty));
        uint16_t empty_mask = 0;  // slots where h2 is empty
        highway::StoreMaskBits(byte_vec_16, cmp_empty, reinterpret_cast<uint8_t*>(&empty_mask));
        std::atomic_thread_fence(std::memory_order_acquire);
        if (empty_mask != 0 &&    // at least one empty
            ((seqn & 1) == 0) &&  // not locked
            g->seq.load(std::memory_order_relaxed) == seqn &&  // hasn't changed
            g->seq.compare_exchange_strong(seqn, seqn + 1)) {  // try lock
          int bit = std::countr_zero(static_cast<unsigned int>(empty_mask));
          g->slots[bit] = entries.make_entry(key, entry);
          g->ctrl[bit] = h2;
          g->seq.store(seqn + 2, std::memory_order_release);
          return {};
        }
      }
    }

    table_version* v = current_version.load(std::memory_order_acquire);
    g_idx = fast_map(h >> 7, v->num_groups);
    g = &(v->groups[g_idx]);

    bool retry = false;
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

      if (retry) {  // delay after first attempt to reduce contention
        volatile int i = 0;
        while (i < 1000) {
          i = i + 1;
        }
      }

      // Now try insert with lock
      uint64_t expected = seq1;
      if (g->seq.load(std::memory_order_relaxed) == seq1 &&
          g->seq.compare_exchange_strong(expected, seq1 + 1,
                                         std::memory_order_acquire)) {
        auto ctrl_val = highway::Load(byte_vec_16, g->ctrl);
        auto cmp_empty =
            highway::Eq(ctrl_val, highway::Set(byte_vec_16, kEmpty));
        uint16_t empty_mask = 0;
        highway::StoreMaskBits(byte_vec_16, cmp_empty, reinterpret_cast<uint8_t*>(&empty_mask));
        if (empty_mask > 0) {
          int bit = std::countr_zero(static_cast<unsigned int>(empty_mask));
          g->slots[bit] = entries.make_entry(key, entry);
          g->ctrl[bit] = h2;
          g->seq.store(seq1 + 2, std::memory_order_release);
          return {};
        }

        // Slots full, insert to overflow
        Node* old_head = g->overflow.load(std::memory_order_relaxed);
        Node* new_node =
            node_pool->New(entries.make_entry(key, entry), old_head);
        g->overflow.store(new_node, std::memory_order_release);
        if (old_head == nullptr && g_idx < 100)
          v->overflow_groups_count.fetch_add(1, std::memory_order_relaxed);
        g->seq.store(seq1 + 2, std::memory_order_release);
        return {};
      }
      retry = true;
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

      // Lock
      uint64_t expected = seq1;
      if (g->seq.load(std::memory_order_relaxed) == seq1 &&
          g->seq.compare_exchange_strong(expected, seq1 + 1,
                                         std::memory_order_acquire)) {
        if (target_slot != -1) {
          Node* oh = g->overflow.load(std::memory_order_relaxed);
          if (oh != nullptr) {
            entries.retire_entry(g->slots[target_slot]);
            g->slots[target_slot] = oh->entry;
            size_t moved_h = hash(Entries::get_key(oh->entry));
            uint8_t moved_h2 = moved_h & 0x7F;
            g->ctrl[target_slot] = moved_h2;
            Node* next_node = oh->next.load(std::memory_order_relaxed);
            g->overflow.store(next_node, std::memory_order_release);
            if (next_node == nullptr && g_idx < 100) {
              v->overflow_groups_count.fetch_sub(1, std::memory_order_relaxed);
            }
            node_pool->Retire(oh);
          } else {
            entries.retire_entry(g->slots[target_slot]);
            g->ctrl[target_slot] = kEmpty;
          }
          g->seq.store(seq1 + 2, std::memory_order_release);
          return result;
        }

        Node* prev = nullptr;
        Node* curr = g->overflow.load(std::memory_order_relaxed);
        while (curr != nullptr) {
          if (KeyEqual{}(Entries::get_key(curr->entry), key)) {
            break;
          }
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
        entries.retire_entry(curr->entry);
        node_pool->Retire(curr);
        g->seq.store(seq1 + 2, std::memory_order_release);
        return result;
      }
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
    constexpr highway::FixedTag<uint8_t, 16> byte_vec_16;

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
        auto ctrl_val_lock = highway::Load(byte_vec_16, g->ctrl);
        auto cmp_empty =
            highway::Eq(ctrl_val_lock, highway::Set(byte_vec_16, kEmpty));
        uint16_t empty_mask = 0;
        highway::StoreMaskBits(byte_vec_16, cmp_empty, reinterpret_cast<uint8_t*>(&empty_mask));
        if (empty_mask > 0) {
          int bit = std::countr_zero(static_cast<unsigned int>(empty_mask));
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

  // --- Iterator Support ---
  template <typename F>
  static void for_each_group_rec(table_version* t, int64_t i, const F& f) {
    Group& g = t->groups[i];
    uint64_t seq = g.seq.load(std::memory_order_acquire);
    if (seq != kForwarded) {
      for (int j = 0; j < 16; j++) {
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
          for_each_group_rec(next, i * kGrowthFactor + j, f);
        }
      }
    }
  }

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
        for_each_group_rec(t, group_num, g);
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

  template <typename F>
  void for_each(const F& f) {
    auto g = [&](const slot_type& e) { f(Entries::get_data(e)); };
    table_version* v = current_version.load();
    parlay::parallel_for(static_cast<int64_t>(v->num_groups),
                         [&](int64_t i) { for_each_group_rec(v, i, g); });
  }
};
}  // end namespace internal

template <typename K, typename V, class Hash = std::hash<K>,
          class KeyEqual = std::equal_to<K>>
struct parlay_unordered_map {
  using Policy = internal::MapPolicy<K, V, Hash, KeyEqual>;
  using Entries =
      std::conditional_t<internal::is_effectively_trivially_copyable_v<
                             typename Policy::value_type>,
                         internal::DirectEntries<Policy>,
                         internal::IndirectEntries<Policy>>;
  using Table = internal::swiss_parlay_table<Entries>;
  std::unique_ptr<Table> t_ptr;
  size_t initial_size;

  // For benchmark compatibility
  using K_ = K;
  using V_ = V;

  parlay_unordered_map() : parlay_unordered_map(1000) {}
  explicit parlay_unordered_map(size_t n)
      : t_ptr(std::make_unique<Table>(n, true)), initial_size(n) {}

  void clear() { t_ptr = std::make_unique<Table>(initial_size, true); }

  int64_t size() const { return t_ptr->size(); }

  bool empty() const { return size() == 0; }
  bool contains(const K& key) { return Find(key).has_value(); }
  int64_t count(const K& key) { return contains(key) ? 1 : 0; }

  using iterator = typename Table::Iterator;
  iterator begin() { return t_ptr->begin(); }
  iterator end() { return t_ptr->end(); }

  std::optional<V> Find(const K& key) { return t_ptr->Find(key); }

  std::optional<V> Insert(const K& key, const V& value) {
    return t_ptr->Insert(std::make_pair(key, value));
  }

  std::optional<V> Remove(const K& key) { return t_ptr->Remove(key); }

  size_t erase(const K& key) { return Remove(key).has_value() ? 1 : 0; }

  std::pair<iterator, bool> insert(const std::pair<K, V>& val) {
    auto res = t_ptr->Insert(val);
    if (res.has_value()) {
      return {t_ptr->find_iterator(val.first), false};
    } else {
      return {t_ptr->find_iterator(val.first), true};
    }
  }

  template <typename F>
  std::optional<V> Upsert(const K& key, const F& f) {
    return t_ptr->upsert(key, f);
  }

  std::optional<V> Upsert(const K& key, const V& value) {
    auto f = [&](std::optional<V> old) { return value; };
    return t_ptr->upsert(key, f);
  }

  template <typename F>
  bool upsert(const K& key, const F& f) {
    Upsert(key, f);
    return true;
  }

  template <typename F>
  void for_each(const F& f) {
    t_ptr->for_each(f);
  }
};

template <typename K, class Hash = std::hash<K>,
          class KeyEqual = std::equal_to<K>>
struct parlay_unordered_set {
  using Policy = internal::SetPolicy<K, Hash, KeyEqual>;
  using Entries =
      std::conditional_t<internal::is_effectively_trivially_copyable_v<
                             typename Policy::value_type>,
                         internal::DirectEntries<Policy>,
                         internal::IndirectEntries<Policy>>;
  using Table = internal::swiss_parlay_table<Entries>;
  std::unique_ptr<Table> t_ptr;
  size_t initial_size;

  parlay_unordered_set() : parlay_unordered_set(1000) {}
  explicit parlay_unordered_set(size_t n)
      : t_ptr(std::make_unique<Table>(n, true)), initial_size(n) {}

  void clear() { t_ptr = std::make_unique<Table>(initial_size, true); }

  int64_t size() const { return t_ptr->size(); }

  bool empty() const { return size() == 0; }
  bool contains(const K& key) { return Find(key); }
  int64_t count(const K& key) { return contains(key) ? 1 : 0; }

  using iterator = typename Table::Iterator;
  iterator begin() { return t_ptr->begin(); }
  iterator end() { return t_ptr->end(); }

  bool Find(const K& key) { return t_ptr->Find(key); }

  bool Insert(const K& key) { return !t_ptr->Insert(key); }

  bool Remove(const K& key) { return t_ptr->Remove(key); }

  template <typename F>
  void for_each(const F& f) {
    t_ptr->for_each(f);
  }
};

}  // namespace parlay

HWY_AFTER_NAMESPACE();

#endif  // THIRD_PARTY_SWISS_PARLAY_UNORDERED_MAP_H_
