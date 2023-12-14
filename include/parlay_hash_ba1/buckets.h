#include "bigatomic.h"

template <class Entry>
struct buckets_struct {

private:
  using K = typename Entry::Key;
  using V = typename Entry::Value;
    
  struct link {
    Entry entry;
    link* next;
    link(Entry entry, link* next) : entry(entry), next(next) {}
  };

  epoch::memory_pool<link>* link_pool;
  bool clear_at_end;

  // Find key in list, return nullopt if not found
  static std::pair<std::optional<Entry>, long> find_in_list(link* nxt, const K& k) {
    long n = 0;
    while (nxt != nullptr && !nxt->entry.equal(k)) {
      nxt = nxt->next;
      n++;
    }
    if (nxt == nullptr) return std::pair(std::nullopt, n);
    else return std::pair(std::optional(nxt->entry), 0);
  }

  link* copy_list(link* nxt) {
    if (nxt == nullptr) return nullptr;
    return link_pool->New(nxt->entry, copy_list(nxt->next));
  }
		
  std::pair<link*, link*> remove_from_list(link* nxt, const K& k) {
    using rtype = std::pair<link*,link*>;
    if (nxt == nullptr) return rtype(nullptr, nullptr);
    else if (nxt->entry.equal(k))
      return rtype(copy_list(nxt->next), nxt); 
    else {
      auto [ptr, rptr] = remove_from_list(nxt->next, k);
      if (ptr == nullptr) return rtype(nullptr, nullptr);
      return rtype(link_pool->New(nxt->entry, ptr), rptr);
    }
  }

  // retires all values of a list
  void retire_list(link* nxt) {
    while (nxt != nullptr) {
      link* tmp = nxt->next;
      link_pool->Retire(nxt);
      nxt = tmp;
    }
  }

  // name is self descritpive
  static long list_length(link* nxt) {
    long len = 0;
    while (nxt != nullptr) {
      len++;
      nxt = nxt->next;
    }
    return len;
  }

public:

  // The structure stored in each bucket.  It includes a pointer to
  // the first link or marker indicating bucket is forwarded.
  struct state {
  private:
    size_t list_head;
  public:
    Entry entry;
    static state forwarded_state() {
      state x;
      x.list_head = 1ul;
      return x;
    }
    state() : list_head(0) {}
	
    bool is_forwarded() const {return list_head == 1ul ;}
    long length() const {return (list_head >> 48) & 255ul ;}
    void inc_length() {list_head += (1ul << 48);}
    void dec_length() {list_head -= (1ul << 48);}
    link* get_head() const {return (link*) (list_head & ((1ul << 48) - 1));}
    void set_head(link* ptr, size_t n) {
      list_head = ((size_t) ptr) | (n << 48);}
      
    bool operator== (const state& h) const {
      if (h.list_head != list_head) return false;
      if (h.length() == 0) return true;
      return (h.entry == entry);
    }

    struct Iterator {
      state s;
      long i;
      link* cur;
      Iterator(state s, long i) : s(s), i(i), cur(nullptr) {}
      Iterator& operator++() {
	if (i == 0) cur = s.get_head();
	else cur = cur->next;
	i++;
	return *this;
      }
      Entry& operator*() {
	if (i == 0) return s.entry;
	else return cur->entry;
      }
      bool operator!=(const Iterator& iterator) const {
	if (i == 0) return iterator.i != 0;
	return cur != iterator.cur;}
    };
    Iterator begin() { return Iterator(*this, 0);}
    Iterator end() { return Iterator(*this, 1);}
  };

  buckets_struct(bool clear_at_end = false) :
    clear_at_end(clear_at_end),
    link_pool(clear_at_end ? new epoch::memory_pool<link>() : &epoch::get_default_pool<link>()) {
    std::cout << sizeof(bucket) << std::endl;}

  ~buckets_struct() {
    if (clear_at_end)
      delete link_pool;
  }

  // one bucket of a sequence of buckets
  using bucket = big_atomic<state>;

  static state get_state(bucket& bck) { return bck.load(); }
  
  static void initialize(bucket& bck) { bck.store(state()); }

  void retire_state(state& s) {
    retire_list(s.get_head());
  }
    
  bool try_mark_as_forwarded(bucket& bck, state old_s) {
    if (bck.cas(old_s, state::forwarded_state())) {
      retire_state(old_s);
      return true;
    }
    return false;
  }

  void mark_as_forwarded(bucket& bck) {
    bck = state::forwarded_state();
  }

  void push_state(state& s, const Entry& entry) {
    long len = s.length();
    if (len == 0) {
      s.entry = entry;
      s.inc_length();
    } else {
      s.set_head(link_pool->New(entry, s.get_head()), 2);
    }
  }

  void pop_state(state& s) {
    if (s.length() == 2)
      link_pool->Retire(s.get_head());
  }

  void push_entry(bucket& bck, const Entry& entry) {
    state s = bck.load();
    push_state(s, entry);
    bck.store(s);
  }

  void clear(bucket& bck) {
    state s = bck.load();
    bck.store(state());
    retire_state(s);
  }

  long length(state& s) {
    if (s.length() <= 1) return s.length();
    return 1 + list_length(s.get_head());
  }

  std::pair<std::optional<Entry>, long> find_in_state(state& s, const K& k) {
    long len = s.length();
    if (len == 0) return std::pair(std::nullopt, len);
    if (s.entry.equal(k))
      return std::pair(std::optional(s.entry), 0);
    auto [x, cnt] = find_in_list(s.get_head(), k);
    return std::pair(x, cnt + 1);
  }

  std::optional<Entry> find(state& s, const K& k) {
    return find_in_state(s, k).first;
  }

    std::pair<std::optional<Entry>,bool> fast_find(state& s, const K& k) {
      long len = s.length();
      if (len == 0) std::pair(std::optional<Entry>(), true);
      if (s.entry.equal(k))
	return std::pair(std::optional(s.entry), true);
      return std::pair(std::optional<Entry>(),false);
    }

  std::pair<std::optional<std::optional<Entry>>, long>
  try_insert(bucket* s, const Entry& entry) {
    //std::cout << "inserting: " << entry.get_key() << std::endl;
    state old_s = s->load();
    state old_ss = s->load();
    //if (!(old_ss == old_s)) std::cout << "yikes" << std::endl;
    if (old_s.is_forwarded())
      return std::pair(std::nullopt, 0);
    auto [x, len] = find_in_state(old_s, entry.get_key());
    // if already in the hash map, then return the current value
    if (x.has_value())
      return std::pair(std::optional(x), len);
    state new_s = old_s;
    push_state(new_s, entry);
    if (s->cas(old_s, new_s)) {
      return std::pair(std::optional(x), len + 1);
    }
    //abort();
    pop_state(new_s);
    // try failed, return std::nullopt to indicate that need to try again
    return std::pair(std::nullopt, 0);
  }

  std::pair<std::optional<Entry>, bool> remove_from_state(state& s, const K& k) {
    using rtype = std::pair<std::optional<Entry>, bool>;
    long len = s.length();
    if (len == 0) {
      return rtype(std::optional<Entry>(), false);
    } else if (len == 1) {
      if (s.entry.equal(k)) {
	s.dec_length();
	return rtype(std::optional(s.entry), false);
      } else return rtype(std::optional<Entry>(), false);
    } else {
      link* l = s.get_head();
      if (s.entry.equal(k)) {
	link* nxt = l->next;
	s.set_head(nxt, (nxt == nullptr) ? 1 : 2);
	s.entry = l->entry;
	return rtype(std::optional<Entry>(s.entry), true);
      } else {
	auto [new_l, r] = remove_from_list(l, k);
	if (r == nullptr)
	  return rtype(std::optional<Entry>(), false);
	s.set_head(new_l, new_l == nullptr ? 1 : 2);
	return rtype(std::optional<Entry>(r->entry), false);
      }
    }
  }

  void retire_after_successful_remove(state& old_s, bool only_one) {
    link* lst = old_s.get_head();
    if (only_one) link_pool->Retire(lst);
    else retire_list(lst);
  }

  void retire_after_unsuccessful_remove(state& new_s, bool only_one) {
    if (!only_one)
      retire_list(new_s.get_head());
  }
	  
  std::optional<std::optional<Entry>> try_remove(bucket* bck, const K& k) {
    state s_old = bck->load();    
    if (s_old.is_forwarded())
      return std::nullopt;
    // if list is empty, then return that no remove needs to be done
    if (s_old.length() == 0)
      return std::optional(std::optional<Entry>());
    state s_new = s_old;
    auto [entry, only_one] = remove_from_state(s_new, k);
    // if list does not contain key, then return that no remove needs to be done
    if (!entry.has_value())
      return std::optional(entry);
    if (bck->cas(s_old, s_new)) {
      // remove succeeded, return value that was removed
      retire_after_successful_remove(s_old, only_one);
      return std::optional(entry);
    }
    retire_after_unsuccessful_remove(s_new, only_one);
    // try failed, return std::nullopt to indicate that need to try again
    return std::nullopt;
  }

  //   template <typename F>
  //   std::optional<bool> try_upsert_bucket(table_version* t, bucket* s, const K& k, F& f) {
  //     head_ptr old_head = s->load();
  //     get_active_bucket(t, s, k, old_head);
  //     link* old_ptr = old_head;
  // #ifndef USE_LOCKS
  //     auto [cnt, new_ptr] = bcks.update_list(old_ptr, k, f);
  //     if (new_ptr == nullptr) {
  //       if (cnt > t->overflow_size) expand_table(t);
  //       new_ptr = bcks.link_pool->New(std::pair(k, f(std::optional<V>())), old_ptr);
  //       if (weak_cas(s, old_head, head_ptr(new_ptr)))
  // 	return true;
  //       bcks.link_pool->Delete(new_ptr);
  //     } else {
  //       if (weak_cas(s, old_head, head_ptr(new_ptr))) {
  // 	bcks.retire_list_n(old_ptr, cnt);
  // 	return false;
  //       }
  //       bcks.retire_list_n(new_ptr, cnt);
  //     }
  // #else  // use try_lock
  //     // update_list must be in a lock, so we first check if an update needs to be done
  //     // at all so we can avoid the lock if not necessary (i.e., key is not in the list).
  //     auto [x, len] = bcks.find_in_list(old_ptr, k);
  //     if (len > t->overflow_size) expand_table(t);
  //     if (!x.has_value()) {
  //       link* new_ptr = bcks.link_pool->New(std::pair(k, f(std::optional<V>())), old_ptr);
  //       if (weak_cas(s, old_head, head_ptr(new_ptr)))
  // 	return std::optional(true); // try succeeded, returing that a new value is inserted
  //       bcks.link_pool->Delete(new_ptr);
  //     } else {
  //       if (get_locks().try_lock((long) s, [=] {
  // 	  if (!(s->load() == old_head)) return false;
  // 	  auto [cnt, new_ptr] = bcks.update_list(old_ptr, k, f);
  // 	  *s = head_ptr(new_ptr);
  // 	  bcks.retire_list_n(old_ptr, cnt);
  // 	  return true;}))
  // 	return std::optional(false); // try succeeded, returning that no new value is inserted
  //     }
  // #endif
  //     // try failed, return std::nullopt to indicate that need to try again
  //     return std::nullopt;
  //   }

};
