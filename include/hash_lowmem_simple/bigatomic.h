#pragma once

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstring>

#include <atomic>
#include <memory>
#include <new>
#include <thread>
#include <type_traits>
#include <utility>

#include <parlay/portability.h>

namespace parlay {

template<typename T, typename Equal = std::equal_to<>>
struct big_atomic;

namespace internal {

#ifdef __cpp_lib_hardware_interference_size

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Winterference-size"

inline constexpr std::size_t CACHE_LINE_ALIGNMENT = 2 * std::hardware_destructive_interference_size;

#pragma GCC diagnostic pop

#else
inline constexpr std::size_t CACHE_LINE_ALIGNMENT = 128;
#endif

// Pretend implementation of P1478R1: Byte-wise atomic memcpy. Technically undefined behavior
// since std::memcpy is not immune to data races, but on most hardware we should be okay. In
// C++26 we can probably do this for real (assuming Concurrency TS 2 is accepted).
PARLAY_INLINE void atomic_load_per_byte_memcpy(void* dest, const void* source, size_t count,
                                               std::memory_order order = std::memory_order_acquire) {
  std::memcpy(dest, source, count);
  std::atomic_thread_fence(order);
}

PARLAY_INLINE void atomic_store_per_byte_memcpy(void* dest, const void* source, size_t count,
                                                std::memory_order order = std::memory_order_release) {
  std::atomic_thread_fence(order);
  std::memcpy(dest, source, count);
}

// Basically std::bit_cast from C++20 but with a slightly different interface. The goal
// is to type pun from a byte representation into a valid object with valid lifetime.
template<typename T>
PARLAY_INLINE T bits_to_object(const char* src) {
  if constexpr (!std::is_trivially_default_constructible_v<T>) {
    struct uninit_ {
      struct empty {};
      union {
        empty empty_;
        T value;
      };
      uninit_() : empty_{} {}
    } holder;
    std::memcpy(&holder.value, src, sizeof(T));
    return holder.value;
  } else {
    T value;
    std::memcpy(&value, src, sizeof(T));
    return value;
  }
}

// A pointer that can be marked and installed with *tagged nullptr* values. Tagged nullptr values
// allow the pointer to logically represent nullptr, i.e., get_ptr() returns nullptr, but secretly
// the value is represented by a 63-bit tag.
//
// If these tags are sequence numbers, then one can create unique nullptrs that do not compare equal
// for the purpose of compare_exchange. That is, they are useful for creating nullptrs that are immune
// to the ABA problem, because one can tell the difference between an old nullptr and a new nullptr.
// This class does not provide the sequence numbers, they must be supplied when constructing the
// tagged nullptr.
//
// All construction is done via factory functions create_ptr and create_tagged_null in order to
// keep marked_ptr as a trivial type.  Marking/unmarking is done via the mark() and unmark()
// member functions, which return a *new marked_ptr*, i.e., they do not mutate in place.
template<typename T>
class marked_ptr {

  static constexpr uintptr_t SEQ_OFFSET = 1;
  static constexpr uintptr_t PTR_OFFSET = 2;

  static constexpr uintptr_t SEQ_MASK = ~((1ULL << SEQ_OFFSET) - 1);
  static constexpr uintptr_t PTR_MASK = ~((1ULL << PTR_OFFSET) - 1);

  static constexpr uintptr_t SEQ_BIT = 1;
  static constexpr uintptr_t MARK_BIT = 1 << 1;

  static_assert((SEQ_MASK & SEQ_BIT) == 0);
  static_assert(alignof(T) >= (MARK_BIT << 1), "Not enough alignment bits to store the marks!");

public:
  // Factory function -- use instead of constructor so that marked_ptr is a trivial type
  static marked_ptr create_ptr(T* ptr) { return marked_ptr{reinterpret_cast<uintptr_t>(ptr)}; }

  // Factory function for "tagged nullptr".  This is for making successively installed nullptrs
  // compare different to avoid ABA.
  static marked_ptr create_tagged_null(uintptr_t num) { return marked_ptr{(num << SEQ_OFFSET) | SEQ_BIT}; }

  // =============================================== Queries ================================================

  [[nodiscard]] bool is_marked() const noexcept { return ((value & SEQ_BIT)) == 0 && ((value & MARK_BIT) != 0); }

  [[nodiscard]] T* get_ptr() const noexcept {
    return (value & SEQ_BIT) ? nullptr : reinterpret_cast<T*>(value & PTR_MASK);
  }

  T* operator->() const noexcept { return get_ptr(); }
  std::add_lvalue_reference_t<T> operator*() { return *get_ptr(); }

  /* implicit */ operator T*() const noexcept { return get_ptr(); }  // NOLINT(google-explicit-constructor)

  constexpr friend bool operator==(marked_ptr left, marked_ptr right) { return left.value == right.value; }
  constexpr friend bool operator!=(marked_ptr left, marked_ptr right) { return left.value != right.value; }

  // ================================== Updates (all return a new ptr) ======================================

  [[nodiscard]] marked_ptr mark() const noexcept {
    assert(get_ptr() != nullptr);
    return marked_ptr{value | MARK_BIT};
  }

  [[nodiscard]] marked_ptr unmark() const noexcept {
    assert(get_ptr() != nullptr);
    return marked_ptr{value & ~MARK_BIT};
  }

  uintptr_t value;
};

static_assert(std::is_standard_layout_v<marked_ptr<int>> && std::is_trivial_v<marked_ptr<int>>);
static_assert(sizeof(marked_ptr<int>) == 8);

template<typename T, typename Equal>
class NodeManager;

template<typename T, typename Equal>
extern inline NodeManager<T, Equal>& node_manager();

template<typename T, typename Equal>
struct big_atomic_node {
  union {
    big_atomic_node* next_;     // Intrusive link for free list
    T value;
  };
  const unsigned owner{node_manager<T, Equal>().my_thread_id()};  // ID of the owning thread
  std::atomic<bool> is_installed{false};
  bool is_protected{false};
  bool was_installed{false};

  big_atomic_node() noexcept : next_{nullptr} {}
  ~big_atomic_node() = default;
};

template<typename T, typename Equal>
class NodeManager {

  using big_atomic_type = big_atomic<T, Equal>;
  using node_type = big_atomic_node<T, Equal>;
  using marked_node_ptr_type = marked_ptr<node_type>;

  // The minimum number of backup nodes to pre-allocate for each thread.  If a thread ever manages to run out, it will
  // allocate another set of this many on top of whatever it already had.  This can only happen if the user spawns
  // more threads, so there should be no allocations after the warmup run if the number of threads stays the same.
  constexpr static std::size_t slab_size = 1024;

  struct NodeMemorySlab {
    std::array<node_type, slab_size> nodes;
    NodeMemorySlab* next_;
  };

  // A basic single-thread private linked list.  The values are required to expose a public next_ field.
  class IntrusiveFreeList {
  public:
    IntrusiveFreeList() : head(nullptr) {}

    void push(node_type* node) noexcept { node->next_ = std::exchange(head, node); }
    node_type* pop() noexcept {
      assert(!empty());
      return std::exchange(head, head->next_);
    }
    [[nodiscard]] bool empty() const noexcept { return head == nullptr; }

    template<typename F>
    void for_each(F&& f) {
      for (auto current = head; current != nullptr; current = current->next_) {
        f(current);
      }
    }

  private:
    node_type* head;
  };

  // The slots are linked together to form a linked list so that threads can scan
  // for the set of currently protected pointers.
  //
  struct alignas(CACHE_LINE_ALIGNMENT) AnnouncementSlot {
    explicit AnnouncementSlot(unsigned thread_id_, bool in_use_) : thread_id(thread_id_), in_use(in_use_) {}

    // Announced node and big_atomic
    std::atomic<node_type*> protected_node{nullptr};

    // Link together all existing slots into a big global linked list
    std::atomic<AnnouncementSlot*> next{nullptr};

    // Private linked lists of free (available) nodes
    IntrusiveFreeList free_nodes{};

    // Private slab allocated nodes.  Slabs are connected in a linked list
    NodeMemorySlab* my_nodes{nullptr};

    // Unique ID for the owner of this slot (not guaranteed to be in order)
    unsigned thread_id;

    // True if this hazard pointer slot is owned by a thread.
    std::atomic<bool> in_use;
  };

  // Find an available hazard slot, or allocate a new one if none available.
  AnnouncementSlot* get_slot() {
    auto current = announcement_list;
    while (true) {
      if (!current->in_use.load() && !current->in_use.exchange(true)) {
        return current;
      }
      if (current->next.load() == nullptr) {
        // thread_ids are not guaranteed to be installed in the linked list in order
        auto my_slot = new AnnouncementSlot{num_threads.fetch_add(1), true};
        AnnouncementSlot* next = nullptr;
        while (!current->next.compare_exchange_weak(next, my_slot)) {
          current = next;
          next = nullptr;
        }
        return my_slot;
      } else {
        current = current->next.load();
      }
    }
  }

  // Give a slot back to the world so another thread can re-use it
  void relinquish_slot(AnnouncementSlot* slot) { slot->in_use.store(false); }

  // A AnnouncementSlotOwner owns exactly one AnnouncementSlot entry in the global linked list
  // of AnnouncementSlots.  On creation, it acquires a free slot from the list, or appends
  // a new slot if all of them are in use.  On destruction, it makes the slot available
  // for another thread to pick up.
  struct AnnouncementSlotOwner {
    explicit AnnouncementSlotOwner(NodeManager<T, Equal>& list_) : list(list_), my_slot(list.get_slot()) {}

    ~AnnouncementSlotOwner() { list.relinquish_slot(my_slot); }

  private:
    NodeManager<T, Equal>& list;

  public:
    AnnouncementSlot* const my_slot;
  };

public:
  // Pre-populate the slot list with P slots, one for each hardware thread
  NodeManager() : announcement_list(new AnnouncementSlot{0, false}) {
    auto current = announcement_list;
    for (unsigned i = 1; i < std::thread::hardware_concurrency(); i++) {
      current->next = new AnnouncementSlot{i, false};
      current = current->next;
    }
    num_threads.store(std::thread::hardware_concurrency());
  }

  NodeManager(const NodeManager&) = delete;
  NodeManager& operator=(const NodeManager&) = delete;

  ~NodeManager() = delete;

  [[nodiscard]] unsigned my_thread_id() const noexcept { return local_data.my_slot->thread_id; }

  marked_node_ptr_type protect_node(const std::atomic<marked_node_ptr_type>& src) noexcept {
    auto& announcement_slot = local_data.my_slot->protected_node;
    auto result = src.load(std::memory_order_acquire);

    while (true) {
      if (result.get_ptr() == nullptr) return result;
      PARLAY_PREFETCH(result.get_ptr(), 0, 0);
      announcement_slot.exchange(result.unmark(), std::memory_order_seq_cst);

      auto current_value = src.load(std::memory_order_acquire);
      if (current_value.get_ptr() == result.get_ptr()) [[likely]] {
        return result;
      } else {
        result = current_value;
      }
    }
  }

  void release() {
    auto& slot = *local_data.my_slot;
    slot.protected_node.store(nullptr, std::memory_order_relaxed);
  }

  PARLAY_INLINE node_type* get_free_node() {
    auto& slot = *local_data.my_slot;
    if (slot.free_nodes.empty()) [[unlikely]] {
      reclaim_free_nodes(slot);
      assert(!slot.free_nodes.empty());
    }
    auto node = slot.free_nodes.pop();
    return node;
  }

  void free_node(node_type* node) {
    auto& slot = *local_data.my_slot;
    slot.free_nodes.push(node);
  }

private:
  PARLAY_NOINLINE PARLAY_COLD void reclaim_free_nodes(AnnouncementSlot& slot) {

    if (slot.my_nodes != nullptr) {

      for_each_node([&](auto node) {
        node->was_installed = node->is_installed.load(std::memory_order_relaxed);
      });

      for_each_slot([&](auto& announcement) {
        node_type* a = announcement.protected_node.load();
        if (a != nullptr && a->owner == slot.thread_id) {
          a->is_protected = true;
        }
      });

      for_each_node([&](auto node) {
        if (!node->was_installed && !node->is_protected) {
          slot.free_nodes.push(node);
        }
        node->is_protected = false;
      });
    }

    // Nothing available even after reclaiming -- need to allocate more nodes.  This should only happen either
    // (a) the first time it is ever used, or (b) when new threads have been spawned since the last use.
    if (slot.free_nodes.empty()) [[unlikely]] {
      assert(slot.my_nodes == nullptr);   // True as long as we have < 300 threads.  Should remove this for a proper release version.
      grow_nodes(slot);
    }
  }

  // Allocate another slab of nodes. This should only occur when the current thread runs out of
  // nodes, meaning there are more threads than the current number can handle.
  void grow_nodes(AnnouncementSlot& slot) {
    auto new_slab = new NodeMemorySlab{{}, slot.my_nodes};
    slot.my_nodes = new_slab;
    for (auto& node : new_slab->nodes) {
      slot.free_nodes.push(&node);
    }
  }

  template<typename F>
  void for_each_slot(F&& f) noexcept(std::is_nothrow_invocable_v<F&, AnnouncementSlot&>) {
    for (auto current = announcement_list; current != nullptr; current = current->next.load()) {
      f(*current);
    }
  }

  template<typename F>
  void for_each_node(F&& f) noexcept(std::is_nothrow_invocable_v<F&, node_type*>) {
    for (auto slab = local_data.my_slot->my_nodes; slab != nullptr; slab = slab->next_) {
      for (auto& node : slab->nodes) {
        f(&node);
      }
    }
  }

  AnnouncementSlot* const announcement_list;
  std::atomic<unsigned> num_threads{0};

  static inline const thread_local AnnouncementSlotOwner local_data{node_manager<T, Equal>()};
};

template<typename T, typename Equal>
NodeManager<T, Equal>& node_manager() {
  alignas(NodeManager<T, Equal>) static char buffer[sizeof(NodeManager<T, Equal>)];
  static auto* list = new (&buffer) NodeManager<T, Equal>{};
  return *list;
}

}  // namespace internal

template<typename T, typename Equal>
struct big_atomic {
  // T must be trivially copyable, but it doesn't have to be trivially default constructible (or
  // even default constructible at all) since we only make copies from what the user gives us
  static_assert(std::is_trivially_copyable_v<T>);
  static_assert(std::is_invocable_r_v<bool, Equal, T&&, T&&>);

  using node_type = internal::big_atomic_node<T, Equal>;
  using marked_node_ptr_type = internal::marked_ptr<node_type>;
  using node_manager_type = internal::NodeManager<T, Equal>;

  friend node_type;
  friend node_manager_type;

public:
  using value_type = T;
  using version_type = int64_t;

  big_atomic() : version(0), backup_value(marked_node_ptr_type::create_ptr(nullptr)), fast_value{} {
    static_assert(std::is_default_constructible_v<T>);
    node_manager();
    new (static_cast<void*>(&fast_value)) T{};
  }

  /* implicit */ big_atomic(const T& t) :  // NOLINT(google-explicit-constructor)
    version(0),
    backup_value(marked_node_ptr_type::create_ptr(nullptr)),
    fast_value{} {
    node_manager();
    new (static_cast<void*>(&fast_value)) T{t};
  }

  PARLAY_INLINE T load() noexcept {
    auto ver = version.load(std::memory_order_acquire);
    alignas(T) char buffer[sizeof(T)];
    internal::atomic_load_per_byte_memcpy(&buffer, &fast_value, sizeof(T));
    auto p = backup_value.load();
    if (!p.is_marked() && ver == version.load(std::memory_order_relaxed)) [[likely]]
      return internal::bits_to_object<T>(buffer);

    return load_indirect(p);
  }

  PARLAY_INLINE void store(const T& desired) {
    auto ver = version.load(std::memory_order_acquire);
    auto new_p = make_node(desired);
    auto old_p = backup_value.exchange(new_p);
    if (old_p.get_ptr() != nullptr)
      old_p->is_installed.store(false, std::memory_order_relaxed);
    try_seqlock_and_store(ver, desired, new_p);
  }

  PARLAY_INLINE bool cas(const T& expected, const T& desired) {
    auto ver = version.load(std::memory_order_acquire);
    alignas(T) char buffer[sizeof(T)];
    marked_node_ptr_type p;
    if (!try_load_indirect(ver, p, buffer)) {
      // If try_load_indirect fails, we know we are racing with a writer, so
      // we can return false.  Note that if we fail here because of a store
      // that was storing the same value, this is a weak failure, i.e., we can
      // only linearize it as a compare_exchange_weak. If we fail due to a
      // concurrent CAS, its always linearizable as a compare_exchange_strong,
      // because CAS always changes the value, and we can just linearize before
      // whichever value was not desired.
      return false;
    }
    // At this point, buffer definitely contains a valid T value
    T current = internal::bits_to_object<T>(buffer);
    if (!Equal{}(current, expected)) return false;
    if (Equal{}(expected, desired)) return true;

    // At this point, either p == nullptr, in which case it is tagged with a
    // sequence number, so we can safely CAS over it without fear of ABA, or
    // p is a non-nullptr, and it is protected, so we can also safely CAS over
    // it without fear of ABA.

    auto new_p = make_node(desired);
    auto old_p = p;

    if ((backup_value.load(std::memory_order_relaxed) == p && backup_value.compare_exchange_strong(p, new_p))) [[likely]] {
      if (old_p.get_ptr() != nullptr)
        old_p->is_installed.store(false, std::memory_order_relaxed);
      try_seqlock_and_store(ver, desired, new_p);
      return true;
    }
    else if (old_p.get_ptr() != nullptr && p.get_ptr() == nullptr) {
      // In this case, the old ptr was replaced with a nullptr, meaning it might actually
      // still be the same value that was just validated and installed. Here, we have to
      // try the CAS again if the value is still the same.
      ver = version.load(std::memory_order_acquire);
      internal::atomic_load_per_byte_memcpy(buffer, &fast_value, sizeof(T));
      if (ver % 2 == 0 && ver == version.load(std::memory_order_relaxed) &&
          Equal{}(internal::bits_to_object<T>(buffer), expected) &&
          backup_value.load(std::memory_order_relaxed) == p &&
          backup_value.compare_exchange_strong(p, new_p)) {

        try_seqlock_and_store(ver, desired, new_p);
        return true;
      }
    }

    free_node(new_p);
    return false;
  }

  ~big_atomic() {
    auto p = backup_value.load();
    if (p.get_ptr() != nullptr) {
      p->is_installed.store(false, std::memory_order_relaxed);
    }
  }

private:

  marked_node_ptr_type make_node(const T& desired) noexcept {
    auto new_node = node_manager().get_free_node();
    new_node->value = desired;
    new_node->is_installed.store(true, std::memory_order_relaxed);
    return marked_node_ptr_type::create_ptr(new_node);
  }

  static void free_node(marked_node_ptr_type ptr) noexcept { node_manager().free_node(ptr.get_ptr()); }

  static void release() noexcept { node_manager().release(); }

  marked_node_ptr_type protect_backup() noexcept { return node_manager().protect_node(backup_value); }


  PARLAY_INLINE T load_indirect(marked_node_ptr_type& p) noexcept {
    [[maybe_unused]] version_type ver;
    alignas(T) char buffer[sizeof(T)];
    while (!try_load_indirect(ver, p, buffer)) {}
    return internal::bits_to_object<T>(buffer);
  }

  // Tries to read the current version, backup ptr, and active value into ver, p, dest (out params)
  //
  // On success, returns true, on failure returns false. This method is guaranteed to succeed if
  // it does not race with an update.  If it races with an update, it may fail.  If it succeeds,
  // then it is guaranteed that either:
  //   (i) p == nullptr and dest contains the active value
  //  (ii) p != nullptr, is protected, and dest contains the active value equal to p.get_ptr()->value
  //
  PARLAY_INLINE bool try_load_indirect(/* out */ version_type& ver, /* out */ marked_node_ptr_type& p, /* out */ char* dest) noexcept {
    p = protect_backup();
    if (p.get_ptr() != nullptr) [[likely]] {
      std::memcpy(dest, &(p.get_ptr()->value), sizeof(T));
      return true;
    }
    ver = version.load(std::memory_order_acquire);
    internal::atomic_load_per_byte_memcpy(dest, &fast_value, sizeof(T));
    p = backup_value.load();
    if (p.get_ptr() == nullptr && ver == version.load(std::memory_order_relaxed)) {
      return true;
    }
    return false;
  }

  bool try_seqlock_and_store(version_type ver, T desired, marked_node_ptr_type p) noexcept {

    while ((ver % 2 == 0) && (ver == version.load(std::memory_order_relaxed))
           && version.compare_exchange_strong(ver, ver + 1)) {

      // We took the SeqLock, try to save the fast value
      internal::atomic_store_per_byte_memcpy(&fast_value, &desired, sizeof(T));
      ver += 2;
      version.store(ver, std::memory_order_release);

      if (backup_value.compare_exchange_strong(p, marked_node_ptr_type::create_tagged_null(ver))) [[likely]] {
        p->is_installed.store(false, std::memory_order_relaxed);
        return true;
      }
      else if (p.get_ptr() == nullptr) {
        // Someone else came in and successfully installed something,
        // so everything is up-to-date.
        return true;
      }

      p = protect_backup();
      if (p.get_ptr() == nullptr) [[unlikely]]
        return true;

      // Someone beat us and installed a new backup value while we were installing
      // the fast value. We need to try and help install the new desired value.
      desired = p->value;
    }
    return false;
  }

  static internal::NodeManager<T, Equal>& node_manager() { return internal::node_manager<T, Equal>(); }

  std::atomic<marked_node_ptr_type> backup_value{0};
  std::atomic<version_type> version{0};
  alignas(std::max_align_t) alignas(T) char fast_value[sizeof(T)];
};

}  // namespace parlay
