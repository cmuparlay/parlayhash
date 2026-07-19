#ifndef THIRD_PARTY_SWISS_PARLAY_8_UNORDERED_MAP_H_
#define THIRD_PARTY_SWISS_PARLAY_8_UNORDERED_MAP_H_

// A highly concurrent, growable hash map and hash set implementation
// using 8-element groups and Abseil GroupPortableImpl bithack techniques.

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

#if !defined(SWISS_PARLAY_8_USE_HIGHWAY)
#if defined(SWISS_PARLAY_USE_HIGHWAY) || defined(SWISS_PARLAY_USE_VECTORS) || defined(USE_HIGHWAY)
#define SWISS_PARLAY_8_USE_HIGHWAY 1
#elif defined(__aarch64__) || defined(__arm__) || defined(_M_ARM64) || defined(_M_ARM)
#define SWISS_PARLAY_8_USE_HIGHWAY 0
#else
#define SWISS_PARLAY_8_USE_HIGHWAY 0
#endif
#endif

#ifdef GOOGLE
#include "third_party/absl/base/no_destructor.h"
#include "third_party/flock/utils/epoch.h"
#include "third_party/parlay/include/parlay/delayed.h"
#include "third_party/parlay/include/parlay/parallel.h"
#include "third_party/parlay/include/parlay/primitives.h"
#include "third_party/parlay/include/parlay/sequence.h"
#include "third_party/parlay/include/parlay/thread_specific.h"
#if SWISS_PARLAY_8_USE_HIGHWAY
#include "third_party/highway/hwy/highway.h"
#endif
#else
#include "hwy/highway.h"
#include <parlay/delayed.h>
#include <parlay/parallel.h>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include <parlay/thread_specific.h>
#include <utils/epoch.h>
#if SWISS_PARLAY_8_USE_HIGHWAY
#include "hwy/highway.h"
#endif
#endif

namespace parlay {
inline int dummy_parlay_init_8 = (parlay::my_thread_id(), 0);

#if SWISS_PARLAY_8_USE_HIGHWAY
HWY_BEFORE_NAMESPACE();
#endif

#define USE_SET

namespace internal {

extern inline auto& get_locks() {
#ifdef GOOGLE
  static absl::NoDestructor<std::vector<std::atomic<bool>>> locks(1ul << 14);
  return *locks;
#else
  static std::vector<std::atomic<bool>> locks(1ul << 14);
  return locks;
#endif
}

template <typename Entries>
struct swiss_parlay_table {

  static constexpr float kFillFactor = 1.4;
  static_assert(kFillFactor >= 1, "Fill factor must be at least 1");

  static constexpr float kRegrowFraction = .4;

  static constexpr size_t kGrowthFactor = 4;
  static_assert((kGrowthFactor & (kGrowthFactor - 1)) == 0,
                "Growth factor must be a power of 2");
  static_assert(kGrowthFactor > 1, "Growth factor must be greater than 1");

  struct Iterator;

  using Policy = typename Entries::Policy;
  using slot_type = typename Entries::Entry;
  using result_type = typename Policy::result_type;
  using value_type = typename Policy::value_type; 
  using K = typename Policy::K;
  using Hash = typename Policy::Hash;
  using KeyEqual = typename Policy::KeyEqual;

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
    return (!get_locks()[idx].load() &&
            get_locks()[idx].compare_exchange_strong(old, true,
                                                     std::memory_order_acquire,
                                                     std::memory_order_relaxed));
  }

  auto release_lock(uint64_t h) {
    constexpr uint64_t mask = (1ul << 14) - 1;
    uint64_t idx = h & mask;
    get_locks()[idx].store(false, std::memory_order_release);
  }

#if SWISS_PARLAY_8_USE_HIGHWAY
  // must be power of 2, and to be portable, no more than 32 (and
  // depending on architecture).
  static constexpr size_t kGroupSize = 16;
  
  // Match `h2` across kGroupSize slots using Highway vector instructions.
  static inline uint64_t match_slots(const uint8_t* ctrl, uint8_t h2) {
    namespace highway = hwy::HWY_NAMESPACE;
    constexpr highway::FixedTag<uint8_t, kGroupSize> byte_vec;
    auto ctrl_val = highway::Load(byte_vec, ctrl);
    auto match_val = highway::Set(byte_vec, h2);
    auto cmp = highway::Eq(ctrl_val, match_val);
    uint64_t mask = 0;
    highway::StoreMaskBits(byte_vec, cmp, reinterpret_cast<uint8_t*>(&mask));
    return mask & ((1ULL << kGroupSize) - 1);
  }

  // Match empty slots across kGroupSize slots using Highway vector instructions.
  static inline uint64_t match_empty_slots(const uint8_t* ctrl) {
    namespace highway = hwy::HWY_NAMESPACE;
    constexpr highway::FixedTag<uint8_t, kGroupSize> byte_vec;
    auto ctrl_val = highway::Load(byte_vec, ctrl);
    auto match_val = highway::Set(byte_vec, kEmpty);
    auto cmp = highway::Eq(ctrl_val, match_val);
    uint64_t mask = 0;
    highway::StoreMaskBits(byte_vec, cmp, reinterpret_cast<uint8_t*>(&mask));
    return mask & ((1ULL << kGroupSize) - 1);
  }

  // Convert a match mask to a slot index.
  static inline int mask_to_slot(uint64_t mask) {
    return std::countr_zero(mask);
  }
#else
  // must be 8 in this case
  static constexpr size_t kGroupSize = 8;

  static constexpr uint64_t kMsbs8Bytes = 0x8080808080808080ULL;
  static constexpr uint64_t kLsbs8Bytes = 0x0101010101010101ULL;

  static inline uint64_t load_ctrl(const uint8_t* ctrl) {
    uint64_t res;
    std::memcpy(&res, ctrl, 8);
    return res;
  }

  // Stanford bithacks / Abseil GroupPortableImpl technique to match `h2` across 8 slots without vectors.
  static inline uint64_t match_slots(const uint8_t* ctrl, uint8_t h2) {
    uint64_t ctrl_val = load_ctrl(ctrl);
    auto x = ctrl_val ^ (kLsbs8Bytes * h2);
    return (x - kLsbs8Bytes) & ~x & kMsbs8Bytes;
  }

  // Stanford bithacks technique to find empty slots.
  static inline uint64_t match_empty_slots(const uint8_t* ctrl) {
    uint64_t ctrl_val = load_ctrl(ctrl);
    return ctrl_val & kMsbs8Bytes;
  }

  // Convert a match mask to a slot index (0 to 7).
  static inline int mask_to_slot(uint64_t mask) {
    return std::countr_zero(mask) >> 3;
  }
#endif

  struct Node {
    slot_type entry;
    std::atomic<Node*> next;
    Node(const slot_type& entry, Node* next) : entry(entry), next(next) {}
  };

  // Holds a group of kGroupSize entries, along with a kGroupSize-byte control block
  struct alignas(32) Group {
    uint8_t ctrl[kGroupSize];
    std::atomic<uint64_t> seq;
    std::atomic<Node*> overflow;
    slot_type slots[kGroupSize];

    Group() : seq(0), overflow(nullptr) {
      std::fill(std::begin(ctrl), std::end(ctrl), kEmpty);  // all empty
    }
  };

  static constexpr uint8_t kEmpty = 0x80;

  static constexpr uint64_t kForwarded = std::numeric_limits<uint64_t>::max();


  struct table_version {
    size_t num_groups;
    Group* groups;
    std::atomic<table_version*> next{nullptr};
    std::atomic<int64_t> overflow_groups_count{0};
    std::atomic<size_t> completed_count{0};
    std::atomic<size_t> copy_counter{0};
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

    ~table_version() {
      std::free(groups);
    }

    int64_t get_overflow_groups_count() const {
      return overflow_groups_count.load(std::memory_order_relaxed);
    }
  };

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
    retire_all_entries(current_version.load());
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
      uint64_t empty_mask = match_empty_slots(g.ctrl);
      int full_slots_count = kGroupSize - std::popcount(empty_mask);
      int overflow_count = 0;
      Node* curr = g.overflow.load(std::memory_order_acquire);
      while (curr != nullptr) {
        overflow_count++;
        curr = curr->next.load(std::memory_order_acquire);
      }
      return full_slots_count + overflow_count;
    }
  }

  int64_t size() const {
    return epoch::with_epoch([&] {
      table_version* curr = current_version.load(std::memory_order_acquire);
      return parlay::reduce(parlay::delayed::tabulate(curr->num_groups, [&](size_t i) {
        return recursive_group_size(curr, i);
      }));
    });
  }

  bool find_in_group(uint64_t seq1, const K& key,
                     const uint8_t h2, Group* g,
                     result_type& result, int& target_slot) {
    uint64_t mask = match_slots(g->ctrl, h2);
    Node* overflow_ptr = g->overflow.load(std::memory_order_acquire);
    
    if (mask == 0 && (overflow_ptr == nullptr)) {
      std::atomic_thread_fence(std::memory_order_acquire);
      if (seq1 == g->seq.load(std::memory_order_relaxed)) {
        return true;
      }
    }

    auto do_find = [&] {
      slot_type res;
      while (mask > 0) {
        int bit = mask_to_slot(mask);
        slot_type e = g->slots[bit];
        std::atomic_thread_fence(std::memory_order_acquire);
        if (seq1 == g->seq.load(std::memory_order_relaxed)) [[likely]] {
          if (KeyEqual{}(Entries::get_key(e), key)) [[likely]] {
            result = Entries::get_result(e);
            target_slot = bit;
            return true;
          }
        } else return false;
        mask &= mask - 1;
      }

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
        std::atomic_thread_fence(std::memory_order_acquire);
        return seq1 == g->seq.load(std::memory_order_relaxed);
      };
      if constexpr (Entries::kNeedsEpochProtection) {
        return search_overflow();
      } else {
        return epoch::with_epoch(search_overflow);
      }
    };

    if constexpr (Entries::kNeedsEpochProtection) {
      if (mask != 0) {
        if constexpr (std::is_pointer_v<typename Entries::Entry>) {
          int bit = mask_to_slot(mask);
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

      result_type result{};
      int target_slot = -1;
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
    Group* g = &(gm.groups[g_idx]);

    if (!is_growing.load(std::memory_order_relaxed)) {
      uint64_t seqn = g->seq.load(std::memory_order_acquire);
      uint64_t mask = match_slots(g->ctrl, h2);
      if (mask != 0) {
        int bit = mask_to_slot(mask);
        result_type result{};
        auto check = [&] {
          slot_type e = g->slots[bit];
          std::atomic_thread_fence(std::memory_order_acquire);
          if (((seqn & 1) == 0) &&
              g->seq.load(std::memory_order_relaxed) == seqn) {
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
      } else {
        uint64_t empty_mask = match_empty_slots(g->ctrl);
        std::atomic_thread_fence(std::memory_order_acquire);
        if (empty_mask != 0 &&
            ((seqn & 1) == 0)) {
          int bit = mask_to_slot(empty_mask);
          slot_type e = entries.make_entry(key, entry);
          if (g->seq.load(std::memory_order_relaxed) == seqn &&
              g->seq.compare_exchange_strong(seqn, seqn + 1)) {
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
      if (!find_in_group(seq1, key, h2, g, result, target_slot))
        continue;

      if (Policy::is_found(result)) {
        return result;
      }

      uint64_t empty_mask = match_empty_slots(g->ctrl);
      slot_type e = entries.make_entry(key, entry);
      uint64_t expected = seq1;
      bool acquired;

      if (empty_mask != 0) {
        int bit = mask_to_slot(empty_mask);
        if ((acquired = try_acquire_lock(h)) &&
            g->seq.load(std::memory_order_relaxed) == seq1 &&
            g->seq.compare_exchange_strong(expected, seq1 + 1,
                                           std::memory_order_acquire)) {
          g->slots[bit] = e;
          g->ctrl[bit] = h2;
          g->seq.store(seq1 + 2, std::memory_order_release);
          release_lock(h);
          return {};
        }
      } else {
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
      if (!find_in_group(seq1, key, h2, g, result, target_slot))
        continue;

      if (!Policy::is_found(result)) {
        return {};
      }

      bool acquired;

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

    Group* g = &(v->groups[g_idx]);

    while (true) {
      forward_if_needed(h, v, g_idx, g);

      uint64_t seq1 = g->seq.load(std::memory_order_acquire);
      if (seq1 % 2 != 0) {
        continue;
      }

      result_type result{};
      int target_slot = -1;
      if (!find_in_group(seq1, key, h2, g, result, target_slot))
        continue;

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

        auto new_val = f(std::nullopt);
        uint64_t empty_mask = match_empty_slots(g->ctrl);
        if (empty_mask != 0) {
          int bit = mask_to_slot(empty_mask);
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

  template <typename F>
  void for_each(const F& f) {
    auto g = [&](const slot_type& e) { f(Entries::get_data(e)); };
    table_version* v = current_version.load();
    parlay::parallel_for(0, static_cast<int64_t>(v->num_groups),
                         [&](int64_t i) { for_each_in_group_rec(v, i, g); });
  }

  static std::vector<slot_type> group_entries(table_version* t, int64_t i) {
    std::vector<slot_type> result;
    auto g = [&](const slot_type& e) { result.push_back(e); };
    for_each_in_group_rec(t, i, g);
    return result;
  }

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

template <typename Policy_>
struct RelocatableEntries {
  using Policy = Policy_;
  using Data = typename Policy::value_type;
  using K = typename Policy::K;

  static constexpr bool kNeedsEpochProtection =
      !is_effectively_trivially_copyable_v<Data>;

  bool clear_at_end;
  epoch::memory_pool<Data>* data_pool;

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

#if SWISS_PARLAY_8_USE_HIGHWAY
HWY_AFTER_NAMESPACE();
#endif

#endif  // THIRD_PARTY_SWISS_PARLAY_8_UNORDERED_MAP_H_
