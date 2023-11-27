// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYHASH_H_
#define PARLAYHASH_H_

#include <optional>
#include "../parlay/primitives.h"
#include "../parlay/sequence.h"
#include "../parlay/delayed.h"
#include "../utils/epoch.h"
#include "../utils/lock.h"
//#include <parlay/primitives.h>
//#include <parlay/sequence.h>
//#include <parlay/delayed.h>
//#include "utils/epoch.h"
//#include "utils/lock.h"

//#define USE_LOCKS 1

namespace parlay {
  
  template <typename K,
	    typename V,
	    class Hash = std::hash<K>,
	    class KeyEqual = std::equal_to<K>>
  struct unordered_map {

    using KV = std::pair<K,V>;
    struct link {
      KV element;
      link* next;
      link(KV element, link* next) : element(element), next(next) {}
    };

    using bucket = std::atomic<link*>;
    

    struct Table {
      parlay::sequence<bucket> table;
      size_t size;
      bucket* get_bucket(const K& k) {
	size_t idx = Hash{}(k) & (size-1u);
	return &table[idx];
      }
      Table(size_t n) {
	int bits = 1 + parlay::log2_up(n);
	size = 1ul << bits;
	table = parlay::sequence<bucket>(size);
      }
    };

    Table hash_table;

    unordered_map(size_t n) : hash_table(Table(n)) {}
    ~unordered_map() {
      auto& table = hash_table.table;
      parlay::parallel_for (0, table.size(), [&] (size_t i) {
         retire_all_list(table[i].load());});
  }

    static std::optional<V> find_in_list(link* nxt, const K& k) {
      while (nxt != nullptr && !KeyEqual{}(nxt->element.first, k))
	nxt = nxt->next;
      if (nxt == nullptr) return {};
      else return nxt->element.second;
    }

    static std::pair<int, link*> remove_from_list(link* nxt, const K& k) {
      if (nxt == nullptr) return std::pair(0, nullptr);
      else if (KeyEqual{}(nxt->element.first, k)) return std::pair(1, nxt->next); 
      else {
	auto [len, ptr] = remove_from_list(nxt->next, k);
	if (len == 0) return std::pair(len, ptr);
	return std::pair(len + 1, epoch::New<link>(nxt->element, ptr));
      }
    }

    template <typename F>
    static std::pair<int, link*> update_list(link* nxt, const K& k, const F& f) {
      if (nxt == nullptr) return std::pair(0, nullptr);
      else if (KeyEqual{}(nxt->element.first, k)) 
	return std::pair(1, epoch::New<link>(std::pair(k,f(nxt->element.second)), nxt->next));
      else {
	auto [len, ptr] = update_list(nxt->next, k, f);
	if (len == 0) return std::pair(len, ptr);
	return std::pair(len + 1, epoch::New<link>(nxt->element, ptr));
      }
    }
    
    static void retire_list(link* nxt, int n) {
      while (n > 0) {
	n--;
	link* tmp = nxt->next;
	epoch::Retire(nxt);
	nxt = tmp;
      }
    }

    static void retire_all_list(link* nxt) {
      while (nxt != nullptr) {
	link* tmp = nxt->next;
	epoch::Retire(nxt);
	nxt = tmp;
      }
    }

    static int list_length(link* nxt) {
      int len = 0;
      while (nxt != nullptr) {
	len++;
	nxt = nxt->next;
      }
      return len;
    }
    
    std::optional<V> find(const K& k) {
      bucket* s = hash_table.get_bucket(k);
      __builtin_prefetch (s);
      return epoch::with_epoch([&] {return find_in_list(s->load(), k);});
    }

    static bool weak_cas(bucket* s, link* old_v, link* new_v) {
#ifndef USE_LOCKS
      return (s->load() == old_v && s->compare_exchange_weak(old_v, new_v));
#else  // use try_lock
      return (get_locks().try_lock((long) s, [=] {
                  if (s->load() != old_v) return false;
		  *s = new_v;
		  return true;}));
#endif
    }
    
    bool insert(const K& k, const V& v) {
      bucket* s = hash_table.get_bucket(k);
      __builtin_prefetch (s);
      return epoch::with_epoch([&] {
	while (true) {
	  link* head = s->load();
	  if (find_in_list(head, k).has_value()) return false;
	  link* new_head = epoch::New<link>(std::pair(k,v), head);
	  if (weak_cas(s, head, new_head)) return true;
	  epoch::Delete(new_head);
        }});
    }

    bool remove(const K& k) {
      bucket* s = hash_table.get_bucket(k);
      __builtin_prefetch (s);
      return epoch::with_epoch([&] {
	while (true) {
	  link* head = s->load();
	  auto [cnt, new_head] = remove_from_list(head, k);
	  if (cnt == 0) return false;
	  if (weak_cas(s, head, new_head)) {
	    retire_list(head, cnt);
	    return true;
	  }
	  retire_list(new_head, cnt - 1);
	}});
    }

    template <typename F>
    bool upsert(const K& k, const F& f) {
      bucket* s = hash_table.get_bucket(k);
      __builtin_prefetch (s);
      return epoch::with_epoch([&] {
        while (true) {
	  link* head = s->load();
#ifndef USE_LOCKS
	  auto [cnt, new_head] = update_list(head, k, f);
	  if (cnt == 0) {
	    new_head = epoch::New<link>(std::pair(k, f(std::optional<V>())), head);
	    if (weak_cas(s, head, new_head)) return true;
	    epoch::Delete(new_head);
	  } else {
	    if (weak_cas(s, head, new_head)) {
	      retire_list(head, cnt);
	      return false;
	    }
	    retire_list(new_head, cnt);
	  }
#else  // use try_lock
	  if (!find_in_list(head, k).has_value()) {
	    link* new_head = epoch::New<link>(std::pair(k, f(std::optional<V>())), head);
	    if (weak_cas(s, head, new_head)) return true;
	    epoch::Delete(new_head);
	  } else {
	    if (get_locks().try_lock((long) s, [=] {
                  if (s->load() != head) return false;
		  auto [cnt, new_head] = update_list(head, k, f);
		  *s = new_head;
		  retire_list(head, cnt);
		  return true;}))
	      return false;
	  }
#endif
	}});
    }

    long size() {
      return parlay::reduce(parlay::map(hash_table.table, [] (bucket& x) {return (long) list_length(x.load());}));
    }

  };

} // namespace parlay
#endif //PARLAYHASH_H_
