#ifndef PARLAY_BIGATOMIC_HASH_LIST
#define PARLAY_BIGATOMIC_HASH_LIST
#define USE_SET

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

  // buffer_size is picked so state fits in a cache line (if it can)
  static constexpr long buffer_size = (sizeof(Entry) > 24) ? 1 : 48 / sizeof(Entry);

  // log_2 of the expected number of entries in a bucket (< buffer_size)
  static constexpr long log_bucket_size =
    (buffer_size == 1) ? 0 : ((buffer_size < 4) ? 1 : ((buffer_size < 8) ? 2 : 3));

  // for overflow lists
  struct link {
    Entry entry;
    link* next;
    link(const Entry& entry, link* next) : entry(entry), next(next) {}
  };

  // for delayed reclamation of links
  static link* new_link(const Entry& entry, link* l) {
    return epoch::New<link>(entry, l); }
  static void retire_link(link* l) { epoch::Retire(l);}

  // Each bucket contains a "state", which consists of a fixed size
  // buffer of entries (buffer_size) and an overflow list.  The first
  // buffer_size entries in the bucket are kept in the buffer, and any
  // overflow goes to the list.  The head stores both the pointer to
  // the overflow list (lower 56 bits) and the number of elements in
  // the buffer, or buffer_size+1 if overfull (top 8 bits).
  struct state {
  public:
    size_t list_head;
    Entry buffer[buffer_size];
    state() : list_head(0) {}
    state(const Entry& e) : list_head(1ul << 48) {
      buffer[0] = e;
    }

    // update overflow list with new ptr (assumes buffer is full)
    state(const state& s, link* ptr) : list_head(((size_t) ptr) |
						 (buffer_size + (ptr != nullptr)) << 48) {
      for (int i=0; i < buffer_size; i++)
	buffer[i] = s.buffer[i];
    }

    // add entry into the buffer at the end (assumes there is space)
    state(const state& s, Entry e) : list_head((s.buffer_cnt() + 1) << 48) {
      for (int i=0; i < s.buffer_cnt(); i++)
	buffer[i] = s.buffer[i];
      buffer[s.buffer_cnt()] = e;
    }

    // remove buffer entry j, replace with first from overflow list (assumes there is overflow)
    state(const state& s, link* ptr, int j) : list_head(((size_t) ptr->next) |
							(buffer_size + (ptr->next != nullptr)) << 48) {
      for (int i=0; i < buffer_size; i++)
	buffer[i] = s.buffer[i];
      buffer[j] = Entry{ptr->entry};
    }

    // remove buffer entry j, replace with last entry in buffer (assumes no overflow)
    state(const state& s, int j) : list_head((s.buffer_cnt() - 1) << 48) {
      for (int i=0; i < s.buffer_cnt(); i++)
	buffer[i] = s.buffer[i];
      buffer[j] = buffer[s.buffer_cnt() - 1];
    }

    // number of entries in buffer, or buffer_size+1 if overflow
    long buffer_cnt() const {return (list_head >> 48) & 255ul ;}

    // number of entries in bucket (includes those in the overflow list)
    long size() const {
      if (buffer_cnt() <= buffer_size) return buffer_cnt();
      return buffer_size + list_length(overflow_list());
    }

    // get the overflow list
    link* overflow_list() const {
      return (link*) (list_head & ((1ul << 48) - 1));}
  };

  struct alignas(64) bucket { // wrapper to ensure alignment
    big_atomic<state> v;
  };

  struct Table {
    // just an array of buckets
    parlay::sequence<bucket> table;
    size_t size;

    // use hash function to get bucket
    big_atomic<state>* get_bucket(const K& k) {
      size_t idx = Entry::hash(k) & (size - 1u);
      return &table[idx].v;
    }
    
    explicit Table(size_t n) {
      unsigned log_num_buckets = parlay::log2_up(n) - log_bucket_size ;
      size = 1ul << log_num_buckets;  // size is a power of 2
      table = parlay::sequence<bucket>(size);
    }
  };

  Table hash_table;

  explicit parlay_hash(size_t n) : hash_table(Table(n)) {}

  // clear all entries and reclaim memory
  void clear() {
    auto& table = hash_table.table;
    parlay::parallel_for(0, table.size(), [&](size_t i) {
      state l = table[i].v.load();
      for (int i=0; i < l.buffer_cnt(); i++)
	l.buffer[i].retire();
      retire_list_all(l.overflow_list()); });
  }
  
  ~parlay_hash() {
    clear();
  }

  // returns std::optional(f(entry)) for entry with given key
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
  // be reclaimed, the head of the new list, and the link that is removed.
  // Returns [0, nullptr, nullptr] if k is not found
  static std::tuple<int, link*, link*> remove_from_list(link* nxt, const K& k) {
    if (nxt == nullptr)
      return std::tuple(0, nullptr, nullptr);
    else if (nxt->entry.equal(k))
      return std::tuple(1, nxt->next, nxt);
    else {
      auto [len, ptr, removed] = remove_from_list(nxt->next, k);
      if (len == 0) return std::tuple(0, nullptr, nullptr);
      return std::tuple(len + 1, new_link(nxt->entry, ptr), removed);
    }
  }

  // retires first n elements of a list, but not the entries
  static void retire_list_n(link* nxt, int n) {
    while (n > 0) {
      n--;
      link* tmp = nxt->next;
      retire_link(nxt);
      nxt = tmp;
    }
  }

  // retires full list and their entries
  static void retire_list_all(link* nxt) {
    while (nxt != nullptr) {
      link* tmp = nxt->next;
      nxt->entry.retire();
      retire_link(nxt);
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

  // find key if it is in the buffer
  int find_in_buffer(const state& s, const K& k) {
    long len = s.buffer_cnt();
    for (long i = 0; i < std::min(len, buffer_size); i++)
      if (s.buffer[i].equal(k))
	return i;
    return -1;
  }

  // find key if in the bucket (state)
  template <typename F>
  auto find_in_bucket(const state& s, const K& k, const F& f)
    -> std::optional<typename std::result_of<F(Entry)>::type>
  {
    long len = s.buffer_cnt();
    for (long i = 0; i < std::min(len, buffer_size); i++)
      if (s.buffer[i].equal(k))
	return std::optional(f(s.buffer[i]));
    if (len <= buffer_size) return std::nullopt;
    return find_in_list(s.overflow_list(), k, f);
  }

  // Finds the entry with the key
  // Returns an optional which is empty if the key is not in the table,
  // and contains f(e) otherwise, where e is the entry matching the key
  template <typename F>
  auto find(const K& k, const F& f)
    -> std::optional<typename std::result_of<F(Entry)>::type>
  {
    auto s = hash_table.get_bucket(k);
    // if entries are direct, then safe to scan the buffer without epoch protection
    if (Entry::Direct) {
      auto [l, tg] = s->ll();
      // search in buffer
      for (long i = 0; i < std::min(l.buffer_cnt(), buffer_size); i++)
	if (l.buffer[i].equal(k))
	  return std::optional(f(l.buffer[i]));
      // if not found and not overfull, then done
      if (l.buffer_cnt() <= buffer_size) return std::nullopt;
      // otherwise need to search overflow, which requires protection
      return epoch::with_epoch([&] {
        // if state has not changed, then just search list
	if (s->lv(tg)) return find_in_list(l.overflow_list(), k, f);
	return find_in_bucket(s->load(), k, f); // otherwise do full search
      });
    } else { // if using indirection always use protection
      __builtin_prefetch(s);
      return epoch::with_epoch([&] () -> std::optional<typename std::result_of<F(Entry)>::type> {
	  return find_in_bucket(s->load(), k, f);});
    }
  }

  // Inserts at key, and does nothing if key already in the table.
  // The constr function construct the entry to be inserted if needed.
  // Returns an optional, which is empty if sucessfully inserted or
  // contains f(e) if not, where e is the entry matching the key.
  template <typename Constr, typename F>
  auto insert(const K& key, const Constr& constr, const F& f)
    -> std::optional<typename std::result_of<F(Entry)>::type>
  {
    using rtype = std::optional<typename std::result_of<F(Entry)>::type>;
    auto s = hash_table.get_bucket(key);
    // if entries are direct, then safe to scan the buffer without epoch protection
    if (Entry::Direct) {
      auto [l, tg] = s->ll();
      // if found in buffer then done
      for (long i = 0; i < std::min(l.buffer_cnt(), buffer_size); i++)
	if (l.buffer[i].equal(key)) return f(l.buffer[i]);
      if (l.buffer_cnt() < buffer_size) { // buffer has space, insert to end of buffer
	Entry entry = constr();
	if (s->sc(tg, state(l, entry))) return std::nullopt;
	entry.retire();
      }
    }
    // if indirect, or not found in buffer and buffer overfull then protect
    return epoch::with_epoch([&] () -> rtype {
      int delay = 200;
      while (true) {
	auto [l, tg] = s->ll();
	long len = l.buffer_cnt();
	// if found in buffer then done
	for (long i = 0; i < std::min(len, buffer_size); i++)
	  if (l.buffer[i].equal(key)) return f(l.buffer[i]);
	if (len < buffer_size) { // buffer has space, insert to end of buffer
	  Entry new_e = constr();
	  if (s->sc(tg, state(l, new_e))) return std::nullopt;
	  new_e.retire(); // if failed need to ty again
	} else if (len == buffer_size) { // buffer full, insert new link
	  link* new_head = new_link(constr(), nullptr);
	  if (s->sc(tg, state(l, new_head))) 
	    return std::nullopt;
	  new_head->entry.retire(); // if failed need to ty again
	  retire_link(new_head);
	} else { // buffer overfull, need to check if in list
	  auto x = find_in_list(l.overflow_list(), key, f);
	  if (x.has_value()) return x; // if in list, then done
	  link* new_head = new_link(constr(), l.overflow_list());
	  if (s->sc(tg, state(l, new_head))) // try to add to head of list
	    return std::nullopt;
	  new_head->entry.retire(); // if failed need to ty again
	  retire_link(new_head);
	}
	for (volatile int i=0; i < delay; i++);
	delay = std::min(2*delay, 5000);
      }
    });
  }

  // Removes entry with given key
  // Returns an optional which is empty if the key is not in the table,
  // and contains f(e) otherwise, where e is the entry that is removed.
  template <typename F>
  auto remove(const K& k, const F& f)
    -> std::optional<typename std::result_of<F(Entry)>::type>
  {
    using rtype = std::optional<typename std::result_of<F(Entry)>::type>;
    auto s = hash_table.get_bucket(k);
    // if entries are direct safe to scan the buffer without epoch protection
    if (Entry::Direct) {
      auto [l, tg] = s->ll();
      if (l.buffer_cnt() <= buffer_size) {
	int i = find_in_buffer(l, k);
	if (i == -1) return std::nullopt;
	if (s->sc(tg, state(l, i))) {
	  rtype r = f(l.buffer[i]);
	  l.buffer[i].retire();
	  return r;
	} // if sc failed, will need to try again
      }
    }
    // if buffer overfull, or indirect, then need to protect
    return epoch::with_epoch([&] () -> rtype {
      int delay = 200;
      while (true) {
        auto [l, tg] = s->ll();
	int i = find_in_buffer(l, k);
	if (i >= 0) { // found in buffer
	  if (l.buffer_cnt() > buffer_size) { // need to backfill from list
	    link* ll = l.overflow_list();
	    if (s->sc(tg, state(l, ll, i))) {
	      rtype r = f(l.buffer[i]);
	      l.buffer[i].retire();
	      retire_link(ll);
	      return r;
	    } // if sc failed, will need to try again
	  } else { // buffer not overfull, can backfill within buffer
	    if (s->sc(tg, state(l, i))) {
	      rtype r = f(l.buffer[i]);
	      l.buffer[i].retire();
	      return r;
	    } // if sc failed, will need to try again
	  }
	} else { // not found in buffer
	  if (l.buffer_cnt() <= buffer_size) // if not overful, then done
	    return std::nullopt;
	  auto [cnt, new_head, removed] = remove_from_list(l.overflow_list(), k);
          if (cnt == 0) // not found in list
	    return std::nullopt;
	  // found and removed from list
          if (s->sc(tg, state(l, new_head))) { 
	    rtype r = f(removed->entry);
	    removed->entry.retire();
            retire_list_n(l.overflow_list(), cnt); // retire old list
            return r;
          } // if sc failed, will need to try again
          retire_list_n(new_head, cnt - 1); // failed, retire new list
	}
	for (volatile int i=0; i < delay; i++);
	delay = std::min(2*delay, 5000);
      }
    });
  }

  // Add all entries in bucket i of table to result.
  template <typename Seq, typename F>
  static void bucket_entries(Table* t, long i, Seq& result, const F& f) {
    state l = t->table[i].v.load();
    for (int i=0; i < std::min(l.buffer_cnt(), buffer_size); i++)
      result.push_back(f(l.buffer[i]));
    link* lnk = l.overflow_list();
    while (lnk != nullptr) {
      result.push_back(f(lnk->entry));
      lnk = lnk->next;
    }
  }

  long size() {
    Table* t = &hash_table;
    return epoch::with_epoch([&] {
      return parlay::reduce(parlay::tabulate(t->size, [&] (size_t i) {
	    return t->table[i].v.load().size();}));});
  }

  template <typename F>
  parlay::sequence<Entry> entries(const F& f) {
    //table_version* t = current_table_version.load();
    Table* t = &hash_table;
    return epoch::with_epoch([&] {
      auto s = parlay::tabulate(t->size, [&] (size_t i) {
        parlay::sequence<Entry> r;
	bucket_entries(t, i, r, f);
	return r;});
      return flatten(s);});
  }

  struct Iterator {
  public:
    using value_type        = typename Entry::Data;
    using iterator_category = std::forward_iterator_tag;
    using pointer           = value_type*;
    using reference         = value_type&;
    using difference_type   = long;

  private:
    std::vector<value_type> entries;
    value_type entry;
    Table* t;
    int i;
    long bucket_num;
    bool single;
    bool end;
    void get_next_bucket() {
      while (entries.size() == 0 && ++bucket_num < t->size)
	bucket_entries(t, bucket_num, entries, [] (const Entry& e) {return e.get_entry();});
      if (bucket_num == t->size) end = true;
    }

  public:
    Iterator(bool end) : i(0), bucket_num(-2l), single(false), end(true) {}
    Iterator(Table* t) : t(t),
      i(0), bucket_num(-1l), single(false), end(false) {
      get_next_bucket();
    }
    Iterator(value_type entry) : entry(entry), single(true), end(false) {}
    Iterator& operator++() {
      if (single) end = true;
      else if (++i == entries.size()) {
	i = 0;
	entries.clear();
	get_next_bucket();
      }
      return *this;
    }
    Iterator& operator++(int) {
      Iterator tmp = *this;
      if (single) end = true;
      else if (++i == entries.size()) {
	i = 0;
	entries.clear();
	get_next_bucket();
      }
      return tmp;
    }
    value_type& operator*() {
      if (single) return entry;
      return entries[i];}
    bool operator!=(const Iterator& iterator) {
      return !(end ? iterator.end : (bucket_num == iterator.bucket_num &&
				     i == iterator.i));
    }
    bool operator==(const Iterator& iterator) {
      return !(*this != iterator);}
  };

  Iterator begin() { return Iterator(&hash_table);}
  Iterator end() { return Iterator(true);}

};

  template <typename K_, typename V_, class Hash = std::hash<K_>, class KeyEqual = std::equal_to<K_>>
  struct IndirectMapEntry {
    using K = K_;
    using V = V_;
    using Data = std::pair<K, V>;
    using Key = std::pair<K,size_t>;
    static constexpr bool Direct = false;
  private:
    Data* ptr;
    static Data* tagged_ptr(const Key& k, const V& v) {
      Data* x = epoch::New<Data>(k.first, v);
      return (Data*) (((k.second >> 48) << 48) | ((size_t) x));
    }
    Data* get_ptr() const {
      return (Data*) (((size_t) ptr) & ((1ul << 48) - 1)); }
  public:
    static unsigned long hash(const Key& k) {return k.second;}
    bool equal(const Key& k) const {
      return (((k.second >> 48) == (((size_t) ptr) >> 48)) &&
	      KeyEqual{}(get_ptr()->first, k.first)); }
    void retire() { epoch::Retire(get_ptr()); }
    V get_value() const { return get_ptr()->second;}
    Data get_entry() const { return *get_ptr();}
    static Key make_key(const K& key) { return Key(key,Hash{}(key));}
    IndirectMapEntry(const Key& k, const V& v) : ptr(tagged_ptr(k, v)) {}
    IndirectMapEntry() {}
  };

  template <typename K_, typename V_, class Hash = std::hash<K_>, class KeyEqual = std::equal_to<K_>>
  struct DirectMapEntry {
    using K = K_;
    using V = V_;
    using Key = K;
    using Data = std::pair<K, V>;
    static const bool Direct = true;
    Data data;
    static unsigned long hash(const Key& k) {return Hash{}(k);}
    bool equal(const Key& k) const {
      return KeyEqual{}(data.first, k); }
    void retire() {}
    static Key make_key(const K& k) {return k;}
    V get_value() const {return data.second;}
    Data get_entry() const { return data;}
    DirectMapEntry(const Key& k, const V& v) : data(Data(k,v)) {}
    DirectMapEntry() {}
  };

  template <typename Entry>
  struct unordered_map_ {
    using map = parlay_hash<Entry>;
    map m;
    static constexpr auto true_f = [] (const Entry& kv) {return true;};
    static constexpr auto identity = [] (const Entry& kv) {return kv;};
    static constexpr auto get_value = [] (const Entry& kv) {return kv.get_value();};

    using K = typename Entry::K;
    using V = typename Entry::V;
    using key_type = K;
    using mapped_type = V;
    using value_type = std::pair<K, V>;
    using iterator = typename map::Iterator;

    unordered_map_(long n) : m(map(n)) {}

    iterator begin() { return m.begin();}
    iterator end() { return m.end();}
    bool empty() { return size() == 0;}
    bool max_size() { return (1ul << 47)/sizeof(Entry);}
    void clear() { m.clear();}
    long size() { return m.size();}

    template <typename F = decltype(identity)>
    auto entries(const F& f = identity) { return m.entries(f);}
    long count(const K& k) { return (contains(k)) ? 1 : 0; }
    bool contains(const K& k) { return find(k, true_f).has_value();}

    template <typename F = decltype(get_value)>
    auto find(const K& k, const F& f = get_value)
      -> std::optional<typename std::result_of<F(Entry)>::type>
    { return m.find(Entry::make_key(k), f); }
    
    bool insert(const K& key, const V& value) {
      auto x = Entry::make_key(key);
      return !m.insert(x, [&] {return Entry(x, value);}, true_f).has_value(); }

    bool remove(const K& k) { //      std::cout << "remove" << std::endl;
      return m.remove(Entry::make_key(k), true_f).has_value(); }

  };

  template <typename K, typename V, class Hash = std::hash<K>, class KeyEqual = std::equal_to<K>>
  using unordered_map_i = unordered_map_<IndirectMapEntry<K, V, Hash, KeyEqual>>;

  template <typename K, typename V, class Hash = std::hash<K>, class KeyEqual = std::equal_to<K>>
  using unordered_map = unordered_map_<DirectMapEntry<K, V, Hash, KeyEqual>>;

  template <typename K_, class Hash = std::hash<K_>, class KeyEqual = std::equal_to<K_>>
  struct IndirectSetEntry {
    using K = K_;
    using Data = K;
    using Key = K;
    static constexpr bool Direct = false;
  private:
    Data* ptr;
    static Data* tagged_ptr(const Key& k) {
      Data* x = epoch::New<Data>(k.first);
      return (Data*) (((k.second >> 48) << 48) | ((size_t) x));
    }
    Data* get_ptr() const {
      return (Data*) (((size_t) ptr) & ((1ul << 48) - 1)); }
  public:
    static unsigned long hash(const Key& k) {return k.second;}
    bool equal(const Key& k) const {
      return (((k.second >> 48) == (((size_t) ptr) >> 48)) &&
	      KeyEqual{}(*get_ptr(), k.first)); }
    void retire() { epoch::Retire(get_ptr()); }
    static Key make_key(const K& key) { return Key(key,Hash{}(key));}
    Data get_entry() const { return *get_ptr();}
    IndirectSetEntry(const Key& k) : ptr(tagged_ptr(k)) {}
    IndirectSetEntry() {}
  };

  template <typename K_, class Hash = std::hash<K_>, class KeyEqual = std::equal_to<K_>>
  struct DirectSetEntry {
    using K = K_;
    using Key = K;
    static const bool Direct = true;
    Key data;
    static unsigned long hash(const Key& k) {return Hash{}(k);}
    bool equal(const Key& k) const {return KeyEqual{}(data, k); }
    void retire() {}
    static Key make_key(const K& k) {return k;}
    Key get_entry() const { return data;}
    DirectSetEntry(const Key& k) : data(k) {}
    DirectSetEntry() {}
  };

  template <typename Entry>
  struct unordered_set_ {
  private:
    using map = parlay_hash<Entry>;
    map m;
    static constexpr auto true_f = [] (const Entry& e) {return true;};
    static constexpr auto identity = [] (const Entry& e) {return e;};
    
  public:
    using key_type = K;
    using value_type = K;
    using iterator = typename map::Iterator;
    
    unordered_set_(long n) : m(map(n)) {}

    iterator begin() { return m.begin();}
    iterator end() { return m.end();}
    bool empty() { return size() == 0;}
    bool max_size() { return (1ul << 47)/sizeof(Entry);}
    void clear() { m.clear();}
    long size() { return m.size();}

    template <typename F = decltype(identity)>
    auto entries(const F& f = identity) { return m.entries(f);}
    long count(const K& k) { return (contains(k)) ? 1 : 0; }
    bool contains(const K& k) { return find(k, true_f).has_value();}

    bool find(const K& k) {
      return m.find(Entry::make_key(k), true_f).has_value(); }
    
    bool insert(const K& key) {
      auto x = Entry::make_key(key);
      return !m.insert(x, [&] {return Entry(x);}, true_f).has_value(); }

    bool remove(const K& k) {
      return m.remove(Entry::make_key(k), true_f).has_value(); }

  };

  template <typename K, class Hash = std::hash<K>, class KeyEqual = std::equal_to<K>>
  using unordered_set_i = unordered_set_<IndirectSetEntry<K, Hash, KeyEqual>>;

  template <typename K, class Hash = std::hash<K>, class KeyEqual = std::equal_to<K>>
  using unordered_set = unordered_set_<DirectSetEntry<K, Hash, KeyEqual>>;
}  // namespace parlay
#endif  // PARLAY_BIGATOMIC_HASH_LIST
