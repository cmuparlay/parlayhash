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

//#include <folly/synchronization/AsymmetricThreadFence.h>
//#include <folly/container/F14Set.h>

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
PARLAY_INLINE void atomic_load_per_byte_memcpy(void* dest, const void* source, size_t count, std::memory_order order = std::memory_order_acquire) {
  std::memcpy(dest, source, count);
  std::atomic_thread_fence(order);
}

PARLAY_INLINE void atomic_store_per_byte_memcpy(void* dest, const void* source, size_t count, std::memory_order order = std::memory_order_release) {
  std::atomic_thread_fence(order);
  std::memcpy(dest, source, count);
}

// Basically std::bit_cast from C++20 but with a slightly different interface. The goal
// is to type pun from a byte representation into a valid object with valid lifetime.
template<typename T>
PARLAY_INLINE T bits_to_object(const char* src) {
  if constexpr(!std::is_trivially_default_constructible_v<T>) {
    struct empty{};
    //union { empty empty_{}; T value; };
    T value;
    std::memcpy(&value, src, sizeof(T));
    return value;
  }
  else {
    T value;
    std::memcpy(&value, src, sizeof(T));
    return value;
  }
}

template<typename T>
class marked_ptr {

  static constexpr uintptr_t MARK_BIT = 1;

  static_assert(alignof(T) >= (MARK_BIT << 1), "Not enough alignment bits to store the marks!");

 public:

  // Factory function -- use instead of constructor so that marked_ptr is a trivial type
  static marked_ptr create_ptr(T* ptr) { return marked_ptr{reinterpret_cast<uintptr_t>(ptr)}; }

  // =============================================== Queries ================================================

  [[nodiscard]] bool is_marked() const noexcept {
    return ((value & MARK_BIT) != 0);
  }

  [[nodiscard]] T* get_ptr() const noexcept {
    return reinterpret_cast<T*>(value & ~MARK_BIT);
  }

  T* operator->() const noexcept { return get_ptr(); }
  std::add_lvalue_reference_t<T> operator*() { return *get_ptr(); }

  /* implicit */ operator T*() const noexcept { return get_ptr(); }         // NOLINT(google-explicit-constructor)

  constexpr friend bool operator==(marked_ptr left, marked_ptr right) { return left.value == right.value; }
  constexpr friend bool operator!=(marked_ptr left, marked_ptr right) { return left.value != right.value; }

  // ================================== Updates (all return a new ptr) ======================================

  [[nodiscard]] marked_ptr mark() const noexcept { return marked_ptr{value | MARK_BIT}; }

  [[nodiscard]] marked_ptr unmark() const noexcept { return marked_ptr{value & ~MARK_BIT}; }

  uintptr_t value;
};

static_assert(std::is_standard_layout_v<marked_ptr<int>> && std::is_trivial_v<marked_ptr<int>>);
static_assert(sizeof(marked_ptr<int>) == 8);


template<typename T, typename Equal = std::equal_to<>>
class NodeManager;

template<typename T, typename Equal = std::equal_to<>>
struct big_atomic_node {
  struct empty_ {};
  union { empty_ empty{}; T value; };
  big_atomic<T, Equal>* src_{nullptr};
  big_atomic_node* next_{nullptr};
  bool currently_installed{false};

  big_atomic_node() noexcept : empty{} { }
  ~big_atomic_node() = default;
};

template<typename T, typename Equal = std::equal_to<>>
extern inline NodeManager<T, Equal>& node_manager();

//
//
template<typename T, typename Equal>
class NodeManager {

  using big_atomic_type = big_atomic<T, Equal>;
  using node_type = big_atomic_node<T, Equal>;
  using marked_node_ptr_type = marked_ptr<node_type>;

  using protected_ptr_set_type = std::unordered_set<node_type*>; //folly::F14FastSet<node_type*>;
  using protected_src_set_type = std::unordered_set<big_atomic_type*>; //folly::F14FastSet<big_atomic_type*>;

  using node_allocator = type_allocator<node_type>;

  // The number of backup nodes to pre-allocate for each thread.  If a thread ever manages to runout, it will
  // allocate another set of this many on top of whatever it already had.  This can only happen if the user spawns
  // more threads, so there should be no allocations after the warmup run if the number of threads stays the same.
  const static inline std::size_t node_batch_size = std::max<std::size_t>(10 * std::thread::hardware_concurrency(), 1024);

  class IntrusiveFreeList {
   public:
    IntrusiveFreeList() : head(nullptr) { }

    void push(node_type* node) noexcept { assert(node != head); node->next_ = std::exchange(head, node); }
    node_type* pop() noexcept { assert(!empty()); return std::exchange(head, head->next_); }
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
    explicit AnnouncementSlot(bool in_use_) : in_use(in_use_) {}

    std::atomic<node_type*> protected_node{nullptr};
    std::atomic<big_atomic_type*> protected_src{nullptr};

    // Link together all existing slots into a big global linked list
    std::atomic<AnnouncementSlot*> next{nullptr};

    // Private linked lists of free (available) and used (unavailable) nodes
    IntrusiveFreeList free_nodes;
    IntrusiveFreeList used_nodes;

    // True if this hazard pointer slot is owned by a thread.
    std::atomic<bool> in_use;


    alignas(CACHE_LINE_ALIGNMENT) protected_ptr_set_type protected_nodes{2 * std::thread::hardware_concurrency()};
    protected_src_set_type protected_srcs{2 * std::thread::hardware_concurrency()};
  };

  // Find an available hazard slot, or allocate a new one if none available.
  AnnouncementSlot* get_slot() {
    auto current = announcement_list;
    while (true) {
      if (!current->in_use.load() && !current->in_use.exchange(true)) {
        return current;
      }
      if (current->next.load() == nullptr) {
        auto my_slot = new AnnouncementSlot{true};
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
  NodeManager() : announcement_list(new AnnouncementSlot{false}) {
    node_allocator::init();
    auto current = announcement_list;
    for (unsigned i = 1; i < std::thread::hardware_concurrency(); i++) {
      current->next = new AnnouncementSlot{false};
      current = current->next;
    }
  }

  NodeManager(const NodeManager&) = delete;
  NodeManager& operator=(const NodeManager&) = delete;

  ~NodeManager() = delete;

  void protect_src(big_atomic_type* const ptr) noexcept {
    local_data.my_slot->protected_src.store(ptr, std::memory_order_seq_cst);
    //folly::asymmetric_thread_fence_light(std::memory_order_seq_cst);
  }

  marked_node_ptr_type protect_node(const std::atomic<marked_node_ptr_type>& src) noexcept {
    auto& announcement_slot = local_data.my_slot->protected_node;
    auto result = src.load(std::memory_order_acquire);

    while (true) {
      if (result.get_ptr() == nullptr) {
        return result;
      }
      PARLAY_PREFETCH(result.get_ptr(), 0, 0);
      //announcement_slot.store(result.unmark(), std::memory_order_seq_cst);
      announcement_slot.exchange(result.unmark(), std::memory_order_seq_cst);
      //folly::asymmetric_thread_fence_light(std::memory_order_seq_cst);

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
    slot.protected_ptr.store(nullptr, std::memory_order_relaxed);
    slot.protected_src.store(nullptr, std::memory_order_relaxed);
  }

  PARLAY_INLINE node_type* get_free_node() {
    auto& slot = *local_data.my_slot;
    if (slot.free_nodes.empty()) [[unlikely]] {
      reclaim_free_nodes(slot);
      assert(!slot.free_nodes.empty());
    }
    auto node = slot.free_nodes.pop();
    slot.used_nodes.push(node);
    assert(node->src_ == nullptr);
    return node;
  }

  // Very restrictive.  You are only allowed to free the most recently allocated node!
  void free_node(node_type* node) {
    auto& slot = *local_data.my_slot;
    auto recent_node = slot.used_nodes.pop();
    assert(node == recent_node);
    node->src_ = nullptr;
    slot.free_nodes.push(node);
  }

 private:


  PARLAY_NOINLINE PARLAY_COLD void reclaim_free_nodes(AnnouncementSlot& slot) {

    if (!slot.used_nodes.empty()) {

      // ============================ Scan all actively announced big_atomics =============================
      //folly::asymmetric_thread_fence_heavy(std::memory_order_seq_cst);
      for_each_slot([&](auto&& announcement) { slot.protected_srcs.insert(announcement.protected_src.load()); });

      // Check whether each used node is still installed in a big_atomic at this moment
      // Try to validate and uninstall if possible.
      slot.used_nodes.for_each([&](auto node) {

        // If the big_atomic containing the node was destroyed, we can reclaim it for free
        if (node->src_ == nullptr) [[unlikely]] {
          node->currently_installed = false;
          return;
        }

        assert(node->src_ != nullptr);
        auto ver = node->src_->version.load(std::memory_order_acquire);

        auto current = node->src_->backup_value.load();
        node->currently_installed = (current.get_ptr() == node);

        // Node is installed but not in cache, try to put it in the cache
        if (node->currently_installed && current.is_marked() &&
            node->src_->try_seqlock_and_store(ver, current->value, current)) {
          current = current.unmark();
        }

        if (node->currently_installed && !current.is_marked() && slot.protected_srcs.count(node->src_) == 0) {
          // Uninstall the node since it is in the cache and the source is not announced.
          auto empty_ptr = marked_node_ptr_type::create_ptr(nullptr);
          node->src_->backup_value.compare_exchange_strong(current, empty_ptr);
          node->currently_installed = false;
        }
      });

      // ============================== Scan all actively announced nodes =================================
      //folly::asymmetric_thread_fence_heavy(std::memory_order_seq_cst);
      for_each_slot([&](auto&& announcement) { slot.protected_nodes.insert(announcement.protected_node.load()); });

      IntrusiveFreeList new_used_nodes;

      while (!slot.used_nodes.empty()) {
        auto node = slot.used_nodes.pop();
        if (!node->currently_installed && slot.protected_nodes.count(node) == 0) {
	  node->src_ = nullptr;
          slot.free_nodes.push(node);  /* Node is not installed and not protected. Free it */
        }
        else {
          new_used_nodes.push(node);
        }
      }

      slot.used_nodes = new_used_nodes;

      slot.protected_srcs.clear();
      slot.protected_nodes.clear();
    }

    // Nothing available even after reclaiming -- need to allocate more nodes.  This should only happen either
    // (a) the first time it is ever used, or (b) when new threads have been spawned since the last use.
    if (slot.free_nodes.empty()) {
      for (unsigned i = 0; i < node_batch_size; i++) {
        slot.free_nodes.push(node_allocator::create());
      }
    }
  }

  template<typename F>
  void for_each_slot(F&& f) noexcept(std::is_nothrow_invocable_v<F&, AnnouncementSlot&>) {
    for (auto current = announcement_list; current != nullptr; current = current->next.load()) {
      f(*current);
    }
  }

  AnnouncementSlot* const announcement_list;

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

  /* implicit */ big_atomic(const T& t) : version(0),       // NOLINT(google-explicit-constructor)
                                          backup_value(marked_node_ptr_type::create_ptr(nullptr)), fast_value{} {
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
    auto num = version.load(std::memory_order_acquire);
    auto new_p = make_node(desired).mark();
    backup_value.store(new_p);
    try_seqlock_and_store(num, desired, new_p);
  }

  PARLAY_INLINE bool cas(const T& expected, const T& desired) {
    protect_this();
    auto p = protect_backup();
    auto ver = version.load(std::memory_order_acquire);
    alignas(T) char buffer[sizeof(T)];
    internal::atomic_load_per_byte_memcpy(&buffer, &fast_value, sizeof(T));

    T current = [&]() {  // Use IIFE since you can't stick [[likely]] on a ternary statement
      if (!p.is_marked() && ver == version.load(std::memory_order_relaxed)) [[likely]]
        return internal::bits_to_object<T>(buffer);
      else
        return load_indirect(p);
    }();

    if (!Equal{}(current, expected)) return false;
    if (Equal{}(expected, desired)) return true;

    auto new_p = make_node(desired).mark();
    auto old_p = p;

    if ((backup_value.load(std::memory_order_relaxed) == p && backup_value.compare_exchange_strong(p, new_p))
        || (p == backup_value.load(std::memory_order_relaxed) && p == old_p.unmark() && backup_value.compare_exchange_strong(p, new_p))) {

      try_seqlock_and_store(ver, desired, new_p);
      return true;
    }
    else {
      free_node(new_p);
      return false;
    }
  }

  ~big_atomic() {
    auto p = backup_value.load();
    if (p.get_ptr() != nullptr) { p->src_ = nullptr; }    // Mark as uninstalled so it can be reclaimed
  }

 private:

  marked_node_ptr_type make_node(const T& desired) noexcept {
    auto new_node = node_manager().get_free_node();
    new_node->value = desired;
    new_node->src_ = this;
    return marked_node_ptr_type::create_ptr(new_node);
  }

  static void free_node(marked_node_ptr_type ptr) noexcept {
    node_manager().free_node(ptr.get_ptr());
  }

  marked_node_ptr_type protect_backup() noexcept {
    return node_manager().protect_node(backup_value);
  }

  void protect_this() noexcept {
    node_manager().protect_src(this);
  }

  PARLAY_INLINE T load_indirect(marked_node_ptr_type& p) noexcept {
    protect_this();
    p = protect_backup();
    if (p.get_ptr() != nullptr) [[likely]] return p->value;
    auto ver = version.load(std::memory_order_acquire);
    alignas(T) char buffer[sizeof(T)];
    internal::atomic_load_per_byte_memcpy(&buffer, &fast_value, sizeof(T));
    p = protect_backup();
    if (!p.is_marked() && ver == version.load(std::memory_order_relaxed))
      return internal::bits_to_object<T>(buffer);
    assert(p.get_ptr() != nullptr);   // After the second try, it is guaranteed that the ptr is
    return p->value;                  // not uninstalled because the big_atomic was protected.
  }

  bool try_seqlock_and_store(version_type num, const T& desired, marked_node_ptr_type p) noexcept {
    if ((num % 2 == 0) && num == version.load(std::memory_order_relaxed) && version.compare_exchange_strong(num, num + 1)) {
      internal::atomic_store_per_byte_memcpy(&fast_value, &desired, sizeof(T));
      version.store(num + 2, std::memory_order_release);
      return backup_value.compare_exchange_strong(p, p.unmark());
    }
    return false;
  }

  static internal::NodeManager<T, Equal>& node_manager() { return internal::node_manager<T, Equal>(); }

  std::atomic<marked_node_ptr_type> backup_value{0};
  std::atomic<version_type> version;
  alignas(std::max_align_t) alignas(T) char fast_value[sizeof(T)];  // Over-align in case copies can use faster instructions on aligned data
};


}  // namespace parlay

