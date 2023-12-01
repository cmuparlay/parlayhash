// ***************************
// Epoch-based memory reclamation
// Supports epoch::with_epoch(F f), which runs f within an epoch.
// as well as:
//     epoch::New<T>(args...)
//     epoch::Retire(T* a)   -- delays destruction and free
//     epoch::Delete(T* a)   -- destructs and frees immediately
// Retire delays destruction and free until no operation that was in a
// with_epoch at the time it was run is still within the with_epoch.
//
// When NDEBUG is not set is checks for corruption before and after
// the structure, and checks for double retires/deletes.  Also
//     epoch::check_ptr(T* a)
// will check that the value "a" points to and was allocated by New
// has not been corrupted.
//
// Supports undoing retires.  This can be useful in transactional
// system in which an operation aborts, and any retires done during
// the operations have to be undone.  In particular Retire returns a
// pointer to a boolean.  Running
//    epoch::undo_retire(bool* x)
// will undo the retire.  Must be run in same with_epoch as the retire
// was run, otherwise it could be too late.  If you don't want to undo
// retires, you can ignore this feature.
//
// New<T>, Retire and Delete use a shared pool for the retired lists,
// which, although not very large, is not cleared until program
// termination.  A private pool can be created with
//     epoch::memory_pool<T> a;
// which then supports a->New(args...), a->Retire(T*) and
// a->Delete(T*).  On destruction of "a", all elements of retired
// lists will be destructed and freed.
//
// Developed as part of parlay project at CMU, intially for flock then
// used for verlib, and parlayhash.
// Current dependence on parlay is just for parlay::my_thread_id() and
// parlay::num_thread_ids() which are from "parlay/thread_specific.h".
// ***************************

#include <atomic>
#include <vector>
#include <limits>
#include "parlay/thread_specific.h"

#ifndef PARLAY_EPOCH_H_
#define PARLAY_EPOCH_H_

#ifndef NDEBUG
// Checks for corruption of bytes before and after allocated structures, as well as double frees.
// Requires some extra memory to pad the front and back of a structure.
#define EpochMemCheck 1
#endif

#define USE_MALLOC 1
#define USE_RESERVE 1

#ifndef USE_MALLOC
#include "parlay/alloc.h"
#endif

// ***************************
// epoch structure
// ***************************

namespace epoch {

  namespace internal {

  inline int worker_id() {return parlay::my_thread_id(); }
  inline int num_workers() {return parlay::num_thread_ids();}
  constexpr int max_num_workers = 1024;

struct alignas(64) epoch_s {

  // functions to run when epoch is incremented
  std::vector<std::function<void()>> before_epoch_hooks;
  std::vector<std::function<void()>> after_epoch_hooks;

  struct alignas(64) announce_slot {
    std::atomic<long> last;
    announce_slot() : last(-1l) {}
  };

  std::vector<announce_slot> announcements;
  std::atomic<long> current_epoch;
  epoch_s() {
    announcements = std::vector<announce_slot>(max_num_workers);
    current_epoch = 0;
  }

  long get_current() {
    return current_epoch.load();
  }

  long get_my_epoch() {
    return announcements[worker_id()].last;
  }

  void set_my_epoch(long e) {
    announcements[worker_id()].last = e;
  }

  int announce() {
    size_t id = worker_id();
    while (true) {
      long current_e = get_current();
      long tmp = current_e;
      // apparently an exchange is faster than a store (write and fence)
      announcements[id].last.exchange(tmp, std::memory_order_seq_cst);
      if (get_current() == current_e) return id;
    }
  }

  void unannounce(size_t id) {
    announcements[id].last.store(-1l, std::memory_order_release);
  }

  void update_epoch() {
    size_t id = worker_id();
    long current_e = get_current();

    // check if everyone is done with earlier epochs
    int workers;
    do {
      workers = num_workers();
      if (workers > max_num_workers) {
	      std::cerr << "number of threads: " << workers
			<< ", greater than max_num_threads: " << max_num_workers << std::endl;
	      abort();
      }
      for (int i=0; i < workers; i++)
	if ((announcements[i].last != -1l) && announcements[i].last < current_e)
	  return;
    } while (num_workers() != workers); // this is unlikely to loop

    // if so then increment current epoch
    for (auto h : before_epoch_hooks) h();
    if (current_epoch.compare_exchange_strong(current_e, current_e+1)) {
      for (auto h : after_epoch_hooks) h();
    }
  }
};

  extern inline epoch_s& get_epoch() {
    static epoch_s epoch;
    return epoch;
  }


// ***************************
// links for retired lists
// ***************************

struct alignas(32) Link {
  Link* next;
  void* value;
  bool skip; // if true indicates the value should not be deleted
  Link(Link* next, void* value, bool skip) : next(next), value(value), skip(skip) {}
};

#ifdef USE_MALLOC
  inline Link* new_link(Link* next, void* value, bool skip) {
    return new Link(next, value, skip);}
  inline void free_link(Link* x) {return free(x);}
#else
  using list_allocator = typename parlay::type_allocator<Link>;
  inline Link* new_link(Link* next, void* value, bool skip) {
    return list_allocator::New(next, value, skip);}
  inline void free_link(Link* x) {return list_allocator::free(x);}
#endif

// ***************************
// type specific pools
// ***************************

using namespace std::chrono;
    
template <typename T>
struct alignas(64) memory_pool {
private:

  //static constexpr double milliseconds_between_epoch_updates = 20.0;
  //using sys_time = time_point<std::chrono::system_clock>;

  // each thread keeps one of these
  struct alignas(256) old_current {
    Link* old;  // linked list of retired items from previous epoch
    Link* current; // linked list of retired items from current epoch
    Link* reserve;  // linked list of items that could be destructed, but delayed so they can be reused
    long reserve_size; // lenght of the reserve list
    long epoch; // epoch on last retire, updated on a retire
    long count; // number of retires so far, reset on updating the epoch
    //sys_time time; // time of last epoch update
    old_current() : old(nullptr), current(nullptr), reserve(nullptr), epoch(0), reserve_size(0) {}
  };

  std::vector<old_current> pools;
    
  // wrapper used so can pad for the memory checked version
  struct wrapper {
#ifdef EpochMemCheck    
    long pad;
    std::atomic<long> head;
    T value;
    std::atomic<long> tail;
#else
    T value;
#endif
  };

  // values used to check for corruption or double delete
  static constexpr long default_val = 10;
  static constexpr long deleted_val = 55;

  // given a pointer to value in a wrapper, return a pointer to the wrapper.
  wrapper* wrapper_from_value(T* p) {
     size_t offset = ((char*) &((wrapper*) p)->value) - ((char*) p);
     return (wrapper*) (((char*) p) - offset);
  }

  // add a pointer to the current list
  bool* add_to_current_list(void* p) {
    auto i = worker_id();
    auto &pid = pools[i];
    advance_epoch(i, pid);
    Link* lnk = new_link(pid.current, p, false);
    pid.current = lnk;
    return &(lnk->skip);
  }

  // Takes items from old that could be destructed and puts them on
  // the reserved list if the list is not too long.  Future
  // allocations can be taken from the reserved list avoiding an
  // actual free and allocate.  Avoids problems with various memory
  // allocators, such as jemalloc.
  void append_to_reserve(old_current& pid) {
    if (pid.old != nullptr) {
      if (pid.reserve_size > 1000)
	clear_list(pid.old);
      else {
	Link* hold_ptr = pid.reserve;
	pid.reserve = pid.old;
	Link* ptr = pid.old;
	pid.reserve_size++;
	while (ptr->next != nullptr) {
	  pid.reserve_size++;
	  ptr = ptr->next;
	}
	ptr->next = hold_ptr;
      }
    }
  }

  // destructs and frees a linked list of objects
  void clear_list(Link* ptr) {
    while (ptr != nullptr) {
      Link* tmp = ptr;
      ptr = ptr->next;
      if (!tmp->skip) Delete((T*) tmp->value);
      free_link(tmp);
    }
  }

  void advance_epoch(int i, old_current& pid) {
    if (pid.epoch + 1 < get_epoch().get_current()) {
#ifdef USE_RESERVE
      append_to_reserve(pid);
#else
      clear_list(pid.old);
#endif
      pid.old = pid.current;
      pid.current = nullptr;
      pid.epoch = get_epoch().get_current();
    }
    // a heuristic
    //auto now = system_clock::now();
    long update_threshold = 10 * num_workers();
    if (++pid.count == update_threshold) {
      //|| duration_cast<milliseconds>(now - pid.time).count() >
      //milliseconds_between_epoch_updates * (1 + ((float) i)/workers)) {
      pid.count = 0;
      //pid.time = now;
      get_epoch().update_epoch();
    }
  }

#ifdef USE_MALLOC
  void free_wrapper(wrapper* x) {return free(x);}
#else
  using Allocator = parlay::type_allocator<wrapper>;
  void free_wrapper(wrapper* x) { return Allocator::free(x);}
#endif

  wrapper* allocate_wrapper() {
#ifdef USE_RESERVE
    auto &pid = pools[worker_id()];
    while (pid.reserve != nullptr && pid.reserve->skip) {
      Link* nxt = pid.reserve;
      free_link(pid.reserve);
      pid.reserve = nxt;
    }
    // take from the reserved list if any available
    if (pid.reserve != nullptr) {
      Link* tmp = pid.reserve;
      pid.reserve = pid.reserve->next;
      pid.reserve_size--;
      T* v = (T*) tmp->value;
      v->~T();
      free_link(tmp); 
      return wrapper_from_value(v);
    }
#endif
#ifdef USE_MALLOC
    return (wrapper*) malloc(sizeof(wrapper));
#else
    return Allocator::alloc();
#endif
  }

public:
  memory_pool() {
    long workers = max_num_workers;
    long update_threshold = 10 * num_workers();
    pools = std::vector<old_current>(workers);
    for (int i = 0; i < workers; i++) {
      pools[i].count = parlay::hash64(i) % update_threshold;
      //pools[i].time = system_clock::now();
    }
  }

  memory_pool(const memory_pool&) = delete;
  ~memory_pool() { clear(); }

  // noop since epoch announce is used for the whole operation
  void acquire(T* p) { }

  // destructs and frees the object immediately
  void Delete(T* p) {
     wrapper* x = wrapper_from_value(p);
#ifdef EpochMemCheck
     // check nothing is corrupted or double deleted
     if (x->head != default_val || x->tail != default_val) {
       if (x->head == deleted_val) std::cerr << "double free" << std::endl;
       else if (x->head != default_val)  std::cerr << "corrupted head" << std::endl;
       if (x->tail != default_val) std::cerr << "corrupted tail" << std::endl;
       abort();
     }
     x->head = deleted_val;
#endif
     p->~T();
     free_wrapper(x);
  }

  template <typename ... Args>
  T* New(Args... args) {
    wrapper* x = allocate_wrapper();
#ifdef EpochMemCheck
    x->pad = x->head = x->tail = default_val;
#endif
    T* newv = &x->value;
    new (newv) T(args...);
    return newv;
  }

  bool check_not_corrupted(T* ptr) {
#ifdef EpochMemCheck
    wrapper* x = wrapper_from_value(ptr);
    if (x->pad != default_val) std::cerr << "memory_pool: pad word corrupted" << std::endl;
    if (x->head != default_val) std::cerr << "memory_pool: head word corrupted" << std::endl;
    if (x->tail != default_val) std::cerr << "memory_pool: tail word corrupted" << std::endl;
    return (x->pad == default_val && x->head == default_val && x->tail == default_val);
#endif
    return true;
  }

  template <typename F, typename ... Args>
  // f is a function that initializes a new object before it is shared
  T* new_init(F f, Args... args) {
    T* x = New(args...);
    f(x);
    return x;
  }

  // retire and return a pointer if want to undo the retire
  bool* Retire(T* p) {
    return add_to_current_list((void*) p);}

  // Clears all the lists, to be used on termination, or could be use
  // at a quiescent point when noone is reading any retired items.
  void clear() {
    get_epoch().update_epoch();
    for (int i=0; i < num_workers(); i++) {
      pools[i].reserve_size = 0;
      clear_list(pools[i].old);
      clear_list(pools[i].current);
      clear_list(pools[i].reserve);
      pools[i].old = pools[i].current = pools[i].reserve = nullptr;
    }
  }
};

} // namespace internal

  // x should point to the skip field of a link
  inline void undo_retire(bool* x) { *x = true;}
  //inline void undo_allocate(bool* x) { *x = false;}
  
  template <typename T>
  using memory_pool = internal::memory_pool<T>;

  template <typename T>
  extern inline memory_pool<T>& get_default_pool() {
    static memory_pool<T> pool;
    return pool;
  }

  template <typename T, typename ... Args>
  static T* New(Args... args) {
    return get_default_pool<T>().New(std::forward<Args>(args)...);}

  template <typename T>
  static void Delete(T* p) {get_default_pool<T>().Delete(p);}

  template <typename T>
  static bool* Retire(T* p) {return get_default_pool<T>().Retire(p);}

  template <typename T>
  static bool check_ptr(T* p) {return get_default_pool<T>().check_not_corrupted(p);}

  template <typename T>
  static void clear() {get_default_pool<T>().clear();}

  //template <typename T>
  //static void stats() {get_default_pool<T>().stats();}

  template <typename Thunk>
  auto with_epoch(Thunk f) {
    int id = internal::get_epoch().announce();
    if constexpr (std::is_void_v<std::invoke_result_t<Thunk>>) {
      f();
      internal::get_epoch().unannounce(id);
    } else {
      auto v = f();
      internal::get_epoch().unannounce(id);
      return v;
    }
  }

} // end namespace epoch

#endif //PARLAY_EPOCH_H_
