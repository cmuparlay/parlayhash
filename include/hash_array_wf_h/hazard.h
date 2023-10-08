#include <atomic>
#include <vector>
#include <limits>

#include "parlay/alloc.h"
#include "parlay/primitives.h"

#ifndef PARLAY_HAZARD_H_
#define PARLAY_HAZARD_H_

#ifndef NDEBUG
// Checks for corruption of bytes before and after allocated structures, as well as double frees.
// Requires some extra memory to pad the front and back of a structure.
#define MemCheck 1
#endif
//#define MemCheck 1

//#define USE_MALLOC 1

// ***************************
// hazard pointer structure
// ***************************

namespace hazard {

  namespace internal {

  inline int worker_id() {return parlay::worker_id(); }
  inline int num_workers() {return parlay::num_workers();}

struct alignas(64) hazard_s {
	
  struct alignas(64) announce_slot {
    std::atomic<void*> hold;
    announce_slot() : hold(nullptr) {}
  };

  std::vector<announce_slot> announcements;

  hazard_s() : announcements(std::vector<announce_slot>(num_workers())) {}

  std::vector<void*> get_announced() {
    std::vector<void*> announced;
    for (int i=0; i < num_workers(); i++) {
      void* a = announcements[i].hold;
      if (a != nullptr)	announced.push_back(a);
    }
    return announced;
  }

  template <typename T>
    std::pair<T*, int> announce(std::atomic<T*>* ptr) {
    size_t id = worker_id();
    while (true) {
      auto x = ptr->load();
      auto y = x;
      announcements[id].hold.exchange((void*) x, std::memory_order_seq_cst);
      if (ptr->load() == y) return std::pair(y, id);
    }
  }

  void unannounce(size_t id) {
    announcements[id].hold.store(nullptr, std::memory_order_relaxed);
  }
};

  extern inline hazard_s& get_hazard() {
    static hazard_s hazard;
    return hazard;
  }

// ***************************
// hazard pools
// ***************************

struct Link {
  Link* next;
  void* value;
};

#ifdef USE_MALLOC
  inline Link* allocate_link_() {return (Link*) malloc(sizeof(Link));}
  inline void free_link(Link* x) {return free(x);}
#else
  using list_allocator = typename parlay::type_allocator<Link>;
  inline Link* allocate_link_() {return list_allocator::alloc();}
  inline void free_link(Link* x) {return list_allocator::free(x);}
#endif

  inline Link* allocate_link(Link* nxt, void* val) {
    Link* l = allocate_link_();
    l->next = nxt; l->value = val;
    return l;
  }

  using namespace std::chrono;

template <typename xT>
struct alignas(64) memory_pool_ {
private:

  static constexpr double milliseconds_between_updates = 20.0;
  long update_threshold;
  using sys_time = time_point<std::chrono::system_clock>;

  // each thread keeps one of these
  struct alignas(256) hlist {
    Link* list; // linked list of retired items 
    long count; // number of retires so far
    sys_time time; // time of last pass of hazard pointers
    hlist() : list(nullptr), count(0) {}
  };

  // only used for debugging (i.e. MemCheck=1).
  struct paddedT {
    long pad;
    std::atomic<long> head;
    xT value;
    std::atomic<long> tail;
  };

  std::vector<hlist> pools;
  int workers;

  void add_to_current_list(void* p) {
    auto i = worker_id();
    auto &pid = pools[i];
    clear_hazard(i, pid);
    pid.list = allocate_link(pid.list, p);
  }

  // destructs and frees a linked list of objects 
  void clear_list(Link* ptr) {
    while (ptr != nullptr) {
      Link* tmp = ptr;
      ptr = ptr->next;
      Delete((T*) tmp->value);
      free_link(tmp);
    }
  }

  void clear_hazard(int i, hlist& pid) {
    if (pid.count++ == 8 *  workers) {
      pid.count = 0;
      Link* ptr = pid.list;
      pid.list = nullptr;
      auto announced = get_hazard().get_announced();
      std::unordered_set<void*> a;
      for (auto x : announced) a.insert((void*) (((size_t) x) & ~1ul));
      while (ptr != nullptr) {
	Link* tmp = ptr;
	ptr = ptr->next;
	if (a.count(tmp->value)) 
	  pid.list = allocate_link(pid.list, tmp->value);
	else Delete((T*) tmp->value);
	free_link(tmp);
      }
    }
  }

#ifdef  MemCheck
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
    pools = std::vector<hlist>(workers);
  }

  memory_pool_(const memory_pool_&) = delete;
  ~memory_pool_() {} // clear(); }
  
  paddedT* pad_from_T(T* p) {
     size_t offset = ((char*) &((paddedT*) p)->value) - ((char*) p);
     return (paddedT*) (((char*) p) - offset);
  }
  
  // destructs and frees the object immediately
  void Delete(T* p) {
    p->~T();
#ifdef MemCheck
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
#ifdef MemCheck
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
#ifdef MemCheck
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
			   
  // retire and return a pointer if want to undo the retire
  void Retire(T* p) {
    add_to_current_list((void*) p);}
  
  // clears all the lists 
  // to be used on termination
  void clear() {
    for (int i=0; i < pools.size(); i++) {
      clear_list(pools[i].list);
      pools[i].list = nullptr;
    }
  }

  void stats() {
#ifndef USE_MALLOC
    Allocator::print_stats();
#endif
  }

};

  template <typename T, typename Thunk>
  auto with_announced(std::atomic<T*>* ptr, Thunk f) {
    auto [p, id] = get_hazard().announce(ptr);
    // if constexpr (std::is_void_v<std::invoke_result_t<Thunk>>) {
    //   f(p);
    //   get_hazard().unannounce(id);
    // } else {
    auto v = f(p);
    get_hazard().unannounce(id);
    return v;
  }

  template <typename T>
  extern inline memory_pool_<T>& get_pool() {
    static memory_pool_<T> pool;
    return pool;
  }

  } // end namespace internal

  template <typename F>
  auto try_loop(const F& f, int delay = 1, const int max_multiplier = 1000) {
    int multiplier = 1;
    int cnt = 0;
    while (true)  {
      if (cnt++ == 100000000ul/(delay*max_multiplier)) {
	std::cerr << "problably in an infinite retry loop" << std::endl;
	abort(); 
      }
      auto r = f();
      if (r.has_value()) return *r;
      multiplier = std::min(2*multiplier, max_multiplier);
      for (volatile int i=0; i < delay * multiplier; i++);
    }
  }

  template <typename T, typename ... Args>
  static T* New(Args... args) {
    return internal::get_pool<T>().New(std::forward<Args>(args)...);}

  template <typename T>
  static void Delete(T* p) {internal::get_pool<T>().Delete(p);}

  template <typename T>
  static void Retire(T* p) {internal::get_pool<T>().Retire(p);}

  template <typename T>
  static bool check_ptr(T* p) {return internal::get_pool<T>().check_not_corrupted(p);}

  template <typename T>  
  static void clear() {internal::get_pool<T>().clear();}

  template <typename T>
  static void stats() {internal::get_pool<T>().stats();}

  template <typename T, typename Thunk>
  static auto with_announced(std::atomic<T*>* ptr, Thunk f) {
    auto [p, id] = internal::get_hazard().announce(ptr);
    auto v = f(p);
    internal::get_hazard().unannounce(id);
    return v;
  }

} // end namespace hazard


#endif //PARLAY_HAZARD_H_
