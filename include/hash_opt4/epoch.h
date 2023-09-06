#include <atomic>
#include <vector>
#include <limits>

#include "parlay/alloc.h"
#include "parlay/primitives.h"

#ifndef PARLAY_EPOCH_H_
#define PARLAY_EPOCH_H_

#ifndef NDEBUG
// Checks for corruption of bytes before and after allocated structures, as well as double frees.
// Requires some extra memory to pad the front and back of a structure.
#define EpochMemCheck 1
#endif
#define EpochMemCheck 1

//#define USE_MALLOC 1

// ***************************
// epoch structure
// ***************************

namespace epoch {

  inline int worker_id() {return parlay::worker_id(); }
  inline int num_workers() {return parlay::num_workers();}

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
    int workers = num_workers();
    announcements = std::vector<announce_slot>(workers);
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
    int workers = num_workers();
    long current_e = get_current();
    bool all_there = true;
    // check if everyone is done with earlier epochs
    for (int i=0; i < workers; i++)
      if ((announcements[i].last != -1l) && announcements[i].last < current_e) {
	all_there = false;
	break;
      }
    // if so then increment current epoch
    if (all_there) {
      for (auto h : before_epoch_hooks) h();
      if (current_epoch.compare_exchange_strong(current_e, current_e+1)) {
	for (auto h : after_epoch_hooks) h();
      }
    }
  }
};

  extern inline epoch_s& get_epoch() {
    static epoch_s epoch;
    return epoch;
  }

// ***************************
// epoch pools
// ***************************

struct Link {
  Link* next;
  bool skip;
  void* value;
};

  // x should point to the skip field of a link
  inline void undo_retire(bool* x) { *x = true;}
  inline void undo_allocate(bool* x) { *x = false;}

#ifdef USE_MALLOC
  inline Link* allocate_link() {return (Link*) malloc(sizeof(Link));}
  inline void free_link(Link* x) {return free(x);}
#else
  using list_allocator = typename parlay::type_allocator<Link>;
  inline Link* allocate_link() {return list_allocator::alloc();}
  inline void free_link(Link* x) {return list_allocator::free(x);}
#endif
  
  using namespace std::chrono;

template <typename xT>
struct alignas(64) memory_pool_ {
private:

  static constexpr double milliseconds_between_epoch_updates = 20.0;
  long update_threshold;
  using sys_time = time_point<std::chrono::system_clock>;

  // each thread keeps one of these
  struct alignas(256) old_current {
    Link* old;  // linked list of retired items from previous epoch
    Link* current; // linked list of retired items from current epoch
    long epoch; // epoch on last retire, updated on a retire
    long count; // number of retires so far, reset on updating the epoch
    sys_time time; // time of last epoch update
    old_current() : old(nullptr), current(nullptr), epoch(0) {}
  };

  // only used for debugging (i.e. EpochMemCheck=1).
  struct paddedT {
    long pad;
    std::atomic<long> head;
    xT value;
    std::atomic<long> tail;
  };

  std::vector<old_current> pools;
  int workers;

  bool* add_to_current_list(void* p) {
    auto i = worker_id();
    auto &pid = pools[i];
    advance_epoch(i, pid);
    Link* lnk = allocate_link();
    lnk->next = pid.current;
    lnk->value = p;
    lnk->skip = false;
    pid.current = lnk;
    return &(lnk->skip);
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
    if (pid.epoch + 2 < get_epoch().get_current()) {
      clear_list(pid.old);
      pid.old = pid.current;
      pid.current = nullptr;
      pid.epoch = get_epoch().get_current();
    }
    // a heuristic
    auto now = system_clock::now();
    if (++pid.count == update_threshold  ||
	duration_cast<milliseconds>(now - pid.time).count() >
	milliseconds_between_epoch_updates * (1 + ((float) i)/workers)) {
      pid.count = 0;
      pid.time = now;
      get_epoch().update_epoch();
    }
  }

#ifdef  EpochMemCheck
  using nodeT = paddedT;
#else
  using nodeT = xT;
#endif

#ifdef USE_MALLOC
  nodeT* allocate_node() {return (nodeT*) malloc(sizeof(nodeT));}
  void free_node(nodeT* x) {return free(x);}
#else
  using Allocator = parlay::type_allocator<nodeT>;
  nodeT* allocate_node() { return Allocator::alloc();}
  void free_node(nodeT* x) { return Allocator::free(x);}
#endif
  
public:
  using T = xT;
  
  memory_pool_() {
    workers = num_workers();
    update_threshold = 10 * workers;
    pools = std::vector<old_current>(workers);
    for (int i = 0; i < workers; i++) {
      pools[i].count = parlay::hash64(i) % update_threshold;
      pools[i].time = system_clock::now();
    }
  }

  memory_pool_(const memory_pool_&) = delete;
  ~memory_pool_() {} // clear(); }

  // noop since epoch announce is used for the whole operation
  void acquire(T* p) { }
  
  paddedT* pad_from_T(T* p) {
     size_t offset = ((char*) &((paddedT*) p)->value) - ((char*) p);
     return (paddedT*) (((char*) p) - offset);
  }
  
  // destructs and frees the object immediately
  void Delete(T* p) {
    p->~T();
#ifdef EpochMemCheck
    paddedT* x = pad_from_T(p);
    if (x->head != 10 || x->tail != 10) {
      if (x->head == 55) std::cerr << "double free" << std::endl;
      else std::cerr << "corrupted head" << std::endl;
      if (x->tail != 10) std::cerr << "corrupted tail" << std::endl;
      std::abort();
    }
    x->head = 55;
    free_node(x);
#else
    free_node(p);
#endif
  }

  template <typename ... Args>
  T* New(Args... args) {
#ifdef EpochMemCheck
    paddedT* x = allocate_node();
    x->pad = x->head = x->tail = 10;
    T* newv = &x->value;
    new (newv) T(args...);
    assert(check_not_corrupted(newv));
#else
    T* newv = allocate_node();
    new (newv) T(args...);
#endif
    return newv;
  }

  bool check_not_corrupted(T* ptr) {
#ifdef EpochMemCheck
    paddedT* x = pad_from_T(ptr);
    if (x->pad != 10 && x->head == 55)
      std::cerr << "memory_pool: apparent use after free" << std::endl;
    else {
      if (x->pad != 10) std::cerr << "memory_pool: pad word corrupted: " << x->pad << std::endl;
      if (x->head != 10) std::cerr << "memory_pool: head word corrupted: " << x->head << std::endl;
    }
    if (x->tail != 10) std::cerr << "memory_pool: tail word corrupted" << std::endl;
    return (x->pad == 10 && x->head == 10 && x->tail == 10);
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
  
  // clears all the lists 
  // to be used on termination
  void clear() {
    get_epoch().update_epoch();
    for (int i=0; i < pools.size(); i++) {
      clear_list(pools[i].old);
      clear_list(pools[i].current);
      pools[i].old = pools[i].current = nullptr;
    }
  }
};

  template <typename Thunk>
  auto with_epoch(Thunk f) {
    int id = get_epoch().announce();
    if constexpr (std::is_void_v<std::invoke_result_t<Thunk>>) {
      f();
      get_epoch().unannounce(id);
    } else {
      auto v = f();
      get_epoch().unannounce(id);
      return v;
    }
  }

  template <typename F>
  auto try_loop(const F& f, int delay = 1, const int max_multiplier = 1000) {
    int multiplier = 1;
    int cnt = 0;
    while (true)  {
      if (cnt++ == 10000000ul/(delay*max_multiplier)) {
	std::cerr << "problably in an infinite retry loop" << std::endl;
	abort(); 
      }
      auto r = f();
      if (r.has_value()) return *r;
      multiplier = std::min(2*multiplier, max_multiplier);
      for (volatile int i=0; i < delay * multiplier; i++);
    }
  }

  template <typename T>
  extern inline epoch::memory_pool_<T>& get_pool() {
    static epoch::memory_pool_<T> pool;
    return pool;
  }

  template <typename T>
  struct memory_pool {
    template <typename ... Args>
    static T* New(Args... args) {
      return get_pool<T>().New(std::forward<Args>(args)...);}
    static void Delete(T* p) {get_pool<T>().Delete(p);}
    static bool* Retire(T* p) {return get_pool<T>().Retire(p);}
    static bool check_not_corrupted(T* p) {return get_pool<T>().check_not_corrupted(p);}
    static void clear() {get_pool<T>().clear();}
  };

} // end namespace epoch

#endif //PARLAY_EPOCH_H_
