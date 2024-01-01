
#ifndef PARLAY_BIGATOMIC_HASH_LIST
#define PARLAY_BIGATOMIC_HASH_LIST
//#define USE_SET

#include <functional>
#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include <utils/epoch.h>
#include "bigatomic.h"

namespace parlay {

template <typename Entry>
struct parlay_hash {
  using K = typename Entry::Key;

  static constexpr long block_size = (sizeof(Entry) > 24) ? 1 : 48 / sizeof(Entry);
  static constexpr long extra_bits = (block_size == 1) ? 0 : ((block_size < 4) ? -1 : ((block_size < 8) ? -2 : -3));

  struct link {
    Entry entry;
    link* next;
    link(const Entry& entry, link* next) : entry(entry), next(next) {}
  };

  struct state {
  public:
    size_t list_head;
    Entry entries[block_size];
    state() : list_head(0) {}
    state(const Entry& e) : list_head(1ul << 48) {
      entries[0] = e;
    }

    // update list with new ptr (assumes buffer is full)
    state(const state& s, link* ptr) : list_head(((size_t) ptr) |
						 (block_size + (ptr != nullptr)) << 48) {
      for (int i=0; i < block_size; i++)
	entries[i] = s.entries[i];
    }

    // add entry into buffer
    state(const state& s, Entry e) : list_head((s.length() + 1) << 48) {
      for (int i=0; i < s.length(); i++)
	entries[i] = s.entries[i];
      entries[s.length()] = e;
    }

    // remove buffer entry j, replace with first from list
    state(const state& s, link* ptr, int j) : list_head(((size_t) ptr->next) |
							(block_size + (ptr->next != nullptr)) << 48) {
      for (int i=0; i < block_size; i++)
	entries[i] = s.entries[i];
      entries[j] = Entry{ptr->entry};
    }

    // remove buffer entry j, replace with last entry in buffer, assumes no list
    state(const state& s, int j) : list_head((s.length() - 1) << 48) {
      for (int i=0; i < s.length(); i++)
	entries[i] = s.entries[i];
      entries[j] = entries[s.length() - 1];
    }

    bool is_empty() const {return list_head == 0ul ;}
    long length() const {return (list_head >> 48) & 255ul ;}
    long size() const {
      if (length() <= block_size) return length();
      return block_size + list_length(get_head());
    }
    
    void inc_length() {list_head += (1ul << 48);}
    void dec_length() {list_head -= (1ul << 48);}
    link* get_head() const {return (link*) (list_head & ((1ul << 48) - 1));}
    void set_head(link* ptr, size_t n) {
      list_head = ((size_t) ptr) | (n << 48);}
  };

  struct alignas(64) bucket {
    big_atomic<state> v;
  };

  struct Table {
    parlay::sequence<bucket> table;
    size_t size;
    big_atomic<state>* get_bucket(const K& k) {
      size_t idx = Entry::hash(k) & (size - 1u);
      return &table[idx].v;
    }
    explicit Table(size_t n) {
      unsigned bits = parlay::log2_up(n) + extra_bits ;
      size = 1ul << bits;
      table = parlay::sequence<bucket>(size);
    }
  };

  Table hash_table;

  static link* new_link(const Entry& entry, link* l) {
    return epoch::New<link>(entry, l); }

  explicit parlay_hash(size_t n) : hash_table(Table(n)) {}
  ~parlay_hash() {
    auto& table = hash_table.table;
    parlay::parallel_for(0, table.size(), [&](size_t i) {
      retire_list_all(table[i].v.load().get_head()); });
  }

  template <typename F>
  static auto find_in_list(const link* nxt, const K& k, const F& f) {
    using rtype = typename std::result_of<F(Entry)>::type;
    while (nxt != nullptr && !nxt->entry.equal(k)) {
      nxt = nxt->next;
    }
    if (nxt == nullptr)
      return std::optional<rtype>();
    else
      return std::optional<rtype>(f(nxt->entry));
  }

  // If k is found copies list elements up to k, and keeps the old
  // tail past k.  Returns the number of new nodes that will need to
  // be reclaimed.  If not found, does nothing, and returns 0.
  static std::tuple<int, link*, link*> remove_from_list(link* nxt, const K& k) {
    if (nxt == nullptr)
      return std::tuple(0, nullptr, nullptr);
    else if (nxt->entry.equal(k))
      return std::tuple(1, nxt->next, nxt);
    else {
      auto [len, ptr, removed] = remove_from_list(nxt->next, k);
      if (len == 0) return std::tuple(len, nullptr, nullptr);
      return std::tuple(len + 1, new_link(nxt->entry, ptr), removed);
    }
  }

  // retires first n elements of a list
  static void retire_list_n(link* nxt, int n) {
    while (n > 0) {
      n--;
      link* tmp = nxt->next;
      epoch::Retire(nxt);
      nxt = tmp;
    }
  }

  static void retire_list_all(link* nxt) {
    while (nxt != nullptr) {
      link* tmp = nxt->next;
      epoch::Retire(nxt);
      nxt = tmp;
    }
  }

  static long list_length(link* nxt) {
    long len = 0;
    while (nxt != nullptr) {
      len++;
      nxt = nxt->next;
    }
    return len;
  }

  int find_in_buffer(const state& s, const K& k) {
    long len = s.length();
    for (long i = 0; i < std::min(len, block_size); i++)
      if (s.entries[i].equal(k))
	return i;
    return -1;
  }

  bool maybe_find_in_buffer(const state& s, const K& k) {
    long len = s.length();
    for (long i = 0; i < std::min(len, block_size); i++)
      if (s.entries[i].equal(k))
	return true;
    return false;
  }

  template <typename F>
  auto find_in_state(const state& s, const K& k, const F& f)
    -> std::optional<typename std::result_of<F(Entry)>::type>
  {
    long len = s.length();
    for (long i = 0; i < std::min(len, block_size); i++)
      if (s.entries[i].equal(k))
	return std::optional(f(s.entries[i]));
    if (len <= block_size) return std::nullopt;
    return find_in_list(s.get_head(), k, f);
  }

  template <typename F>
  auto find(const K& k, const F& f)
    -> std::optional<typename std::result_of<F(Entry)>::type>
  {
    auto s = hash_table.get_bucket(k);
    //if (s->load().is_empty()) return std::nullopt;
    //if (!maybe_find_in_buffer(s->load(),k)) return std::nullopt;
    __builtin_prefetch(s);
    return epoch::with_epoch([&] () -> std::optional<typename std::result_of<F(Entry)>::type> {
			       return find_in_state(s->load(), k, f);
    auto [l, tg] = s->ll();
    for (long i = 0; i < std::min(l.length(), block_size); i++)
      if (l.entries[i].equal(k)) 
	return std::optional(f(l.entries[i]));
    if (l.length() <= block_size) return std::nullopt;
    //return epoch::with_epoch([&] {
      if (s->lv(tg)) return find_in_list(l.get_head(), k, f);
	return find_in_state(s->load(), k, f);
      });
  }

  bool insert(const K& key, const Entry& entry) {
    auto s = hash_table.get_bucket(key);
    //auto [l, tg] = s->ll();
    //if (l.length() < block_size && !maybe_find_in_buffer(l, key))
    //  if (s->sc(tg, state(l, entry))) return true;
    //__builtin_prefetch(s);
    return epoch::with_epoch([&] {
      int delay = 200;
      while (true) {
	auto [l, tg] = s->ll();
	long len = l.length();
	if (l.is_empty()) {
	  if (s->sc(tg, state(entry))) return true;
	} else {
	  for (long i = 0; i < std::min(len, block_size); i++)
	    if (l.entries[i].equal(key)) return false;
	  if (len < block_size) {
	    if (s->sc(tg, state(l, entry))) return true;
	  } else if (len == block_size) {
	    link* new_head = new_link(entry, nullptr);
	    if (s->sc(tg, state(l, new_head))) 
	      return true;
	    epoch::Delete(new_head);
	  } else {
	    if (find_in_list(l.get_head(), key,
			     [] (const Entry e) {return true;}).has_value())
	      return false;
	    link* new_head = new_link(entry, l.get_head());
	    if (s->sc(tg, state(l, new_head))) return true;
	    epoch::Delete(new_head);
	  }
        }
	for (volatile int i=0; i < delay; i++);
	delay = std::min(2*delay, 5000);
      }
    });
  }

  bool remove(const K& k) {
    auto s = hash_table.get_bucket(k);
    return epoch::with_epoch([&] {
      int delay = 200;
      while (true) {
        auto [l, tg] = s->ll();
	int i = find_in_buffer(l, k);
	if (i >= 0) {
	  if (l.length() > block_size) {
	    link* ll = l.get_head();
	    if (s->sc(tg, state(l, ll, i))) {
	      l.entries[i].retire();
	      epoch::Retire(ll);
	      return true;
	    }
	  } else {
	    if (s->sc(tg, state(l, i))) {
	      l.entries[i].retire();
	      return true;
	    }
	  }
	} else {
	  if (l.length() <= block_size) return false;
	  auto [cnt, new_head, removed] = remove_from_list(l.get_head(), k);
          if (cnt == 0) return false;
          if (s->sc(tg, state(l, new_head))) {
	    removed->entry.retire();
            retire_list_n(l.get_head(), cnt);
            return true;
          }
          retire_list_n(new_head, cnt - 1);
	}
	for (volatile int i=0; i < delay; i++);
	delay = std::min(2*delay, 5000);
      }
    });
  }

  long size() {
    return parlay::reduce(parlay::map(hash_table.table, [&](bucket& x) { return x.v.load().size(); }));
  }
};

  template <typename K, typename V, class Hash = std::hash<K>, class KeyEqual = std::equal_to<K>>
  struct unordered_map {

    struct Data {
      K key;
      V value;
      Data(const K& key, const V& value) : key(key), value(value) {}
    };

    using Key = std::pair<K,size_t>;
    
    struct Entry {
      using Key = typename unordered_map::Key;
      Data* ptr;
      static Data* tagged_ptr(const Key& k, const V& v) {
	Data* x = epoch::New<Data>(k.first, v);
	return (Data*) (((k.second >> 48) << 48) | ((size_t) x));
      }
      Data* get_ptr() const {
	return (Data*) (((size_t) ptr) & ((1ul << 48) - 1)); }
      static unsigned long hash(const Key& k) {return k.second;}
      bool equal(const Key& k) const {
	return (((k.second >> 48) == (((size_t) ptr) >> 48)) &&
		KeyEqual{}(get_ptr()->key, k.first)); }
      bool maybe_equal(const Key& k) const {
	return ((k.second >> 48) == (((size_t) ptr) >> 48));}
      void retire() { epoch::Retire(get_ptr()); }
      Entry(const Key& k, const V& v) : ptr(tagged_ptr(k, v)) {}
      Entry() {}
    };

    using map = parlay_hash<Entry>;
    map m;
    static constexpr auto get_value = [] (const Entry& kv) {return kv.get_ptr()->value;};

    using key_type = K;
    using mapped_type = V;
    using value_type = std::pair<K, V>;
    Key make_key(const K& key) { return Key(key,Hash{}(key));}

    unordered_map(long n) : m(map(n)) {}

    bool empty() {return size() == 0;}
    bool max_size() {return (1ul << 47)/sizeof(Entry);}
    void clear() {m.clear();}
    long size() { return m.size();}
    long count(const K& k) { return (contains(k)) ? 1 : 0; }
    bool contains(const K& k) { return Find(k).has_value();}

    template <typename F = decltype(get_value)>
    auto find(const K& k, const F& f = get_value)
      -> std::optional<typename std::result_of<F(Entry)>::type>
    { //std::cout << "find" << std::endl;
      return m.find(make_key(k), f); }
    
    bool insert(const K& key, const V& value) {
      //std::cout << "insert" << std::endl;
      auto x = make_key(key);
      //std::cout << "insert2" << std::endl;
      return m.insert(x, Entry(x, value)); }

    bool remove(const K& k) { //      std::cout << "remove" << std::endl;
      return m.remove(make_key(k)); }

  };

  // template <typename K, class Hash = std::hash<K>, class KeyEqual = std::equal_to<K>>
  // struct unordered_set {

  //   struct Entry {
  //     using Key = K;
  //     K key;
  //     static unsigned long hash(const K& k) {return Hash{}(k);}
  //     bool equal(const K& k) const {return KeyEqual{}(key, k);}
  //     const K& get_key() const {return key;}
  //     Entry(const K& k) : key(k) {}
  //     Entry() {}
  //   };

  //   using map = parlay_hash<Entry>;
  //   map m;
  //   static constexpr auto truef = [] (const Entry& kv) {return true;};

  //   using key_type = K;
  //   using value_type = K;

  //   unordered_set(long n) : m(map(n)) {}

  //   bool empty() {return size() == 0;}
  //   bool max_size() {return (1ul << 47)/sizeof(Entry);}
  //   void clear() {m.clear();}
  //   long size() { return m.size();}
  //   long count(const K& k) { return (contains(k)) ? 1 : 0; }
  //   bool contains(const K& k) { return Find(k).has_value();}

  //   bool find(const K& k) { return m.find(k, truef).has_value(); }
    
  //   bool insert(const K& key) { return m.insert(Entry{key}); }

  //   bool remove(const K& k) { return m.remove(k); }

  // };

}  // namespace parlay
#endif  // PARLAY_BIGATOMIC_HASH_LIST
