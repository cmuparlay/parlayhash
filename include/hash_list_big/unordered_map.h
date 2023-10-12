// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYHASH_H_
#define PARLAYHASH_H_

#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include "smr/epoch.h"
#include "bigatomic.h"

namespace parlay {
  
  template <typename K,
	    typename V,
	    class Hash = std::hash<K>,
	    class KeyEqual = std::equal_to<K>>
  struct unordered_map {

    struct link {
      K key;
      V value;
      link* next;
      link(const K& key, const V& value, link* next) : key(key), value(value), next(next) {}
      link() : next((link*) 1) {}
      bool operator==(const link& o) const {
	return key == o.key && value == o.value && next == o.next;};
    };

    static link* set_empty() {return (link*) 1;}
    static bool is_empty(const link* ptr) {return 1ul == (1ul & (size_t) ptr);}
    static link* strip_empty(const link* ptr) {return (link*) (~1ul & (size_t) ptr);}

    struct alignas(64) bucket { atomic<link> v;};

    struct Table {
      parlay::sequence<bucket> table;
      size_t size;
      atomic<link>* get_bucket(const K& k) {
	size_t idx = Hash{}(k) & (size-1u);
	return &table[idx].v;
      }
      Table(size_t n) {
	int bits = 1 + parlay::log2_up(n);
	size = 1ul << bits;
	table = parlay::sequence<bucket>(size);
      }
    };

    Table hash_table;

    static link* new_link(const K& k, const V& v, link* l) {
      return epoch::New<link>(k, v, l);
    }

    unordered_map(size_t n) : hash_table(Table(n)) {}
    ~unordered_map() {
      auto& table = hash_table.table;
      parlay::parallel_for (0, table.size(), [&] (size_t i) {
         retire_list_all(table[i].v.load().next);});
  }

    static std::optional<V> find_in_list(const link* nxt, const K& k) {
      while (nxt != nullptr && !KeyEqual{}(nxt->key, k)) {
	nxt = nxt->next;
      }
      if (nxt == nullptr) return {};
      else return nxt->value;
    }

    // If k is found copies list elements up to k, and keeps the old
    // tail past k.  Returns the number of new nodes that will need to
    // be reclaimed.  If not found, does nothing, and returns 0.
    static std::pair<int, link*> remove_from_list(link* nxt, const K& k) {
      if (nxt == nullptr) return std::pair(0, nullptr);
      else if (KeyEqual{}(nxt->key, k)) return std::pair(1, nxt->next); 
      else {
	auto [len, ptr] = remove_from_list(nxt->next, k);
	if (len == 0) return std::pair(len, ptr);
	return std::pair(len + 1, new_link(nxt->key, nxt->value, ptr));
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
      if (is_empty(nxt)) return;
      while (nxt != nullptr) {
	link* tmp = nxt->next;
	epoch::Retire(nxt);
	nxt = tmp;
      }
    }

    static long list_length(const link& l) {
      link* nxt = l.next;
      if (is_empty(nxt)) return 0l;
      long len = 1;
      while (nxt != nullptr) {
	len++;
	nxt = nxt->next;
      }
      return len;
    }

    std::optional<V> find(const K& k) {
      auto s = hash_table.get_bucket(k);
      link l = s->load();
      if (is_empty(l.next)) return {};
      if (KeyEqual{}(l.key, k)) return l.value;
      return epoch::with_epoch([&] () -> std::optional<V> {
        link l = s->load();
	if (is_empty(l.next)) return {};
	if (KeyEqual{}(l.key, k)) return l.value;
	return find_in_list(l.next, k);});
    }

    bool insert(const K& k, const V& v) {
      auto s = hash_table.get_bucket(k);
      __builtin_prefetch (s);
      return epoch::with_epoch([&] {
	long cnt = 0;
	while (true) {
	  link l = s->load();
	  if (is_empty(l.next)) {
	    if (s->cas(l, link(k, v, nullptr))) return true;
	  } else {
	    if (KeyEqual{}(l.key, k)) return false;
	    if (find_in_list(l.next, k).has_value()) return false;
	    link* new_head = new_link(l.key, l.value, l.next);
	    if (s->cas(l, link(k, v, new_head))) return true;
	    epoch::Delete(new_head);
	  }
	  if (cnt++ > 1000000) {std::cout << "insert infinite loop?" << std::endl; abort();} 
	}});
    }

    bool remove(const K& k) {
      auto s = hash_table.get_bucket(k);
      __builtin_prefetch (s);
      return epoch::with_epoch([&] {
	long cnt = 0;
	while (true) {
	  link l = s->load();
	  if (is_empty(l.next)) return false;
	  if (KeyEqual{}(l.key, k)) {
	    if (l.next == nullptr) {
	      if (s->cas(l, link()))
		return true;
	    } else {
	      if (s->cas(l, link(l.next->key, l.next->value, l.next->next))) {
		epoch::Retire(l.next);
		return true;
	      }
	    }
	  } else {
	    auto [cnt, new_head] = remove_from_list(l.next, k);
	    if (cnt == 0) return false;
	    if (s->cas(l, link(l.key, l.value, new_head))) {
	      retire_list_n(l.next, cnt);
	      return true;
	    }
	    retire_list_n(new_head, cnt - 1);
	  }
	  if (cnt++ > 1000000) {std::cout << "remove infinite loop?" << std::endl; abort();} 
	}});
    }

    long size() {
      return parlay::reduce(parlay::map(hash_table.table, [&] (bucket& x) {
							    return list_length(x.v.load());}));
    }

  };

} // namespace parlay
#endif //PARLAYHASH_H_
