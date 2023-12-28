
namespace parlay {
  
template <class Entry>
struct buckets_struct {
  private:
  using K = typename Entry::Key;
    
    struct link {
      Entry element;
      link* next;
      link(Entry element, link* next) : element(element), next(next) {}
    };

    epoch::memory_pool<link>* link_pool;
    bool clear_at_end;

    // Find key in list, return nullopt if not found
    static std::pair<Entry*,long> find_in_list(link* nxt, const K& k) {
      long n = 0;
      while (nxt != nullptr && !nxt->element.equal(k)) {
	nxt = nxt->next;
	n++;
      }
      if (nxt == nullptr) return std::pair(nullptr, n);
      else return std::pair(&nxt->element, 0);
    }

    // Remove key from list using path copying (i.e. does not update any links, but copies
    // path up to the removed link).
    // Returns a triple consisting of the position of the key in the list (1 based),
    // the head of the new list with the key removed, and a pointer to the link with the key.
    // If the key is not found, returns (0, nullptr, nullptr).
    std::tuple<int, link*, link*> remove_from_list(link* nxt, const K& k) {
      if (nxt == nullptr) return std::tuple(0, nullptr, nullptr);
      else if (nxt->element.equal(k))
	return std::tuple(1, nxt->next, nxt); 
      else {
	auto [len, ptr, rptr] = remove_from_list(nxt->next, k);
	if (len == 0) return std::tuple(0, nullptr, nullptr);
	return std::tuple(len + 1, link_pool->New(nxt->element, ptr), rptr);
      }
    }

    // Update element with a given key in a list.  Uses path copying.
    // Returns a pair consisting of the position of the key in the list (1 based), and
    // the head of the new list with the key updated.
    // If the key is not found, returns (l, nullptr), where l is the length of the list.
    template <typename F>
    std::pair<int, link*> update_list(link* nxt, const K& k, const F& f) {
      if (nxt == nullptr) return std::pair(0, nullptr);
      else if (nxt->element.equal(k))
	return std::pair(1, link_pool->New(f(nxt->element), nxt->next));
      else {
	auto [len, ptr] = update_list(nxt->next, k, f);
	if (ptr == nullptr) return std::pair(len + 1, nullptr);
	return std::pair(len + 1, link_pool->New(nxt->element, ptr));
      }
    }

    // retires the first n elements of a list
    void retire_list_n(link* nxt, int n) {
      while (n > 0) {
	n--;
	link* tmp = nxt->next;
	link_pool->Retire(nxt);
	nxt = tmp;
      }
    }

    // retires all elements of a list
    void retire_list(link* nxt) {
      while (nxt != nullptr) {
	link* tmp = nxt->next;
	link_pool->Retire(nxt);
	nxt = tmp;
      }
    }

    // name is self descritpive
    static int list_length(link* nxt) {
      int len = 0;
      while (nxt != nullptr) {
	len++;
	nxt = nxt->next;
      }
      return len;
    }

    // The structure stored in each bucket.  It includes a pointer to
    // the first link or marker indicating bucket is forwarded.
    struct head_ptr {
      size_t ptr;
      static head_ptr forwarded_link() {return head_ptr((link*) 1ul);}
      bool is_forwarded() {return ptr == 1ul ;}
      bool is_empty() {return ptr == 0 ;}
      head_ptr(link* ptr) : ptr((size_t) ptr) {}
      operator link*() {return (link*) ptr;}
      bool operator ==(const head_ptr h) {return ptr == h.ptr;}
      struct Iterator {
	link* cur;
	Iterator(link* cur) : cur(cur) {}
	Iterator& operator++() {cur = cur->next; return *this;}
	Entry& operator*() {return cur->element;}
	bool operator!=(Iterator& iterator) {return cur != iterator.cur;}
      };
      Iterator begin() { return Iterator((link*) ptr);}
      Iterator end() { return Iterator(nullptr);}
    };

    // If using locks, acts like std::compare_exchange_weak, i.e., can fail
    // even if old_v == s->load() since it uses a try lock.
    // If lock free, then will always succeed if equal
    static bool weak_cas(std::atomic<head_ptr>* s, head_ptr old_v, head_ptr new_v) {
#ifndef USE_LOCKS
      return (s->load() == old_v && s->compare_exchange_strong(old_v, new_v));
#else  // use try_lock
      return (get_locks().try_lock((long) s, [=] {
					       if (!(s->load() == old_v)) return false;
					       *s = new_v;
					       return true;}));
#endif
    }

  public:
    buckets_struct(bool clear_at_end = false) :
      clear_at_end(clear_at_end),
      link_pool(clear_at_end ? new epoch::memory_pool<link>() : &epoch::get_default_pool<link>()) {}

    ~buckets_struct() {
      if (clear_at_end)
	delete link_pool;
    }

    // one bucket of a sequence of buckets
    using bucket = std::atomic<head_ptr>;
    using state = head_ptr;

    static state get_state(bucket& bck) { return bck.load(); }
  
    static void initialize(bucket& bck) { bck = nullptr; }
  
    bool try_mark_as_forwarded(bucket& bck, state old_s) {
      if (bck.compare_exchange_strong(old_s, head_ptr::forwarded_link())) {
	retire_list((link*) old_s);
	return true;
      }
      return false;
    }

    void mark_as_forwarded(bucket& bck) {
      bck = head_ptr::forwarded_link();
    }

    void push_entry(bucket& bck, Entry key_value) {
      link* ptr = bck.load();
      bck = link_pool->New(key_value, ptr);
    }

    bool try_push_if_empty(bucket& bck, Entry key_value) {
      link* ptr = bck.load();
      if (ptr == nullptr) {
	head_ptr new_l = link_pool->New(key_value, nullptr);
	head_ptr old_l = nullptr;
	if (bck.compare_exchange_strong(old_l, new_l))
	  return true;
	link_pool->Retire(new_l);
      }
      return false;
    }

    void clear(bucket& bck) {
      head_ptr bucket = bck.load();
      bck = nullptr;
      retire_list(bucket);
    }

    long length(state& s) {
      return list_length(s);
    }

    static Entry* find(state& s, const K& k) {
      return find_in_list(s, k).first;
    }

    std::pair<std::optional<Entry*>, long>
    try_insert(bucket* s, const Entry& entry) {
      head_ptr old_head = s->load();    
      if (old_head.is_forwarded()) return std::pair(std::nullopt, 0);
      link* old_ptr = old_head;
      auto [x, len] = find_in_list(old_ptr, entry.get_key());
      // if (len > t->overflow_size) expand_table(t);
      // if already in the hash map, then return the current value
      if (x != nullptr) 
	return std::pair(std::optional(x), len);
      link* new_ptr = link_pool->New(entry, old_ptr);
      head_ptr new_head = new_ptr;
      if (weak_cas(s, old_head, new_head))
	// successfully inserted
	return std::pair(std::optional(nullptr), len + 1);
      link_pool->Delete(new_ptr);
      // try failed, return std::nullopt to indicate that need to try again
      return std::pair(std::nullopt, 0);
    }

    std::optional<Entry*> try_remove(bucket* s, const K& k) {
      head_ptr old_head = s->load();    
      if (old_head.is_forwarded()) return std::nullopt;
      link* old_ptr = old_head;
      // if list is empty, then return that no remove needs to be done
      if (old_ptr == nullptr) return std::optional(nullptr);
      auto [cnt, new_ptr, val_ptr] = remove_from_list(old_ptr, k);
      // if list does not contain key, then return that no remove needs to be done
      if (cnt == 0) return std::optional(nullptr);
      if (weak_cas(s, old_head, head_ptr(new_ptr))) {
	// remove succeeded, return value that was removed
	retire_list_n(old_ptr, cnt);
	return std::optional(&val_ptr->element);
      }
      retire_list_n(new_ptr, cnt - 1);
      // try failed, return std::nullopt to indicate that need to try again
      return std::nullopt;
    }

  template <typename F>
  std::pair<std::optional<bool>, long>
  try_upsert(bucket* s, const K& k, F& f) {
    head_ptr old_head = s->load();
    if (old_head.is_forwarded()) return std::pair(std::nullopt, 0);
    link* old_ptr = old_head;
#ifndef USE_LOCKS
    auto [cnt, new_ptr] = update_list(old_ptr, k, f);
    if (new_ptr == nullptr) {
      new_ptr = link_pool->New(f(std::optional<Entry>()), old_ptr);
      if (weak_cas(s, old_head, head_ptr(new_ptr)))
	return std::pair(std::optional(true), cnt+1);
      link_pool->Delete(new_ptr);
    } else {
      if (weak_cas(s, old_head, head_ptr(new_ptr))) {
	retire_list_n(old_ptr, cnt);
	return std::pair(std::optional(false), cnt);
      }
      retire_list_n(new_ptr, cnt);
    }
#else  // use try_lock
    // update_list must be in a lock, so we first check if an update needs to be done
    // at all so we can avoid the lock if not necessary (i.e., key is not in the list).
    auto [x, cnt] = find_in_list(old_ptr, k);
    if (!x.has_value()) {
      link* new_ptr = link_pool->New(f(std::optional<Entry>()), old_ptr);
      if (weak_cas(s, old_head, head_ptr(new_ptr)))
	return std::pair(std::optional(true), cnt + 1); // try succeeded, returing that a new element is inserted
      link_pool->Delete(new_ptr);
    } else {
      if (get_locks().try_lock((long) s, [=] {
	  if (!(s->load() == old_head)) return false;
	  auto [cnt, new_ptr] = update_list(old_ptr, k, f);
	  *s = head_ptr(new_ptr);
	  retire_list_n(old_ptr, cnt);
	  return true;}))
	return std::pair(std::optional(false), cnt); // try succeeded, returning that no new element is inserted
    }
#endif
    // try failed, return std::nullopt to indicate that need to try again
    return std::pair(std::nullopt, 0);
  }

  };
} // end namespace parlay
