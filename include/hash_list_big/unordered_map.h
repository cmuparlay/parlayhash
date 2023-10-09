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
#include "bigatomic/wf_loadonly/bigatomic.h"

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
      link(const KV& element, link* next) : element(element), next(next) {}
      link() : next((link*) 1) {}
    };

    struct LinkEqual {
      std::size_t operator()(const link &x, const link& y) const noexcept {
	return (x.element == y.element && x.next == y.next);
      }
    };

    static link* set_empty() {return (link*) 1;}
    static bool is_empty(const link* ptr) {return 1ul == (1ul & (size_t) ptr);}
    static link* strip_empty(const link* ptr) {return (link*) (~1ul & (size_t) ptr);}

    using bucket = atomic<link,LinkEqual>;

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

    static link* new_link(const KV& e, link* l) {
      //if (is_empty(l)) {std::cout << "bad l in new_link" << std::endl; abort();}
      return epoch::New<link>(e, l);
    }

    unordered_map(size_t n) : hash_table(Table(n)) {}
    ~unordered_map() {
      auto& table = hash_table.table;
      parlay::parallel_for (0, table.size(), [&] (size_t i) {
         retire_all_list(table[i].load().next);});
  }

    static std::optional<V> find_in_list(const link* nxt, const K& k) {
      //if (is_empty(nxt)) {std::cout << "bad nxt in new_link" << std::endl; abort();}
      while (nxt != nullptr && !KeyEqual{}(nxt->element.first, k)) {
	nxt = nxt->next;
	//if (is_empty(nxt)) {std::cout << "bad nxt in new_link." << std::endl; abort();}
      }
      if (nxt == nullptr) return {};
      else return nxt->element.second;
    }

    static std::pair<int, link*> remove_from_list(link* nxt, const K& k) {
      //if (is_empty(nxt)) {std::cout << "empty nxt in remove_from_list" << std::endl; abort();}
      if (nxt == nullptr) return std::pair(0, nullptr);
      else if (KeyEqual{}(nxt->element.first, k)) return std::pair(1, nxt->next); 
      else {
	//if (is_empty(nxt->next)) {std::cout << "empty nxt->next in remove_from_list" << std::endl; abort();}
	auto [len, ptr] = remove_from_list(nxt->next, k);
	if (len == 0) return std::pair(len, ptr);
	return std::pair(len + 1, new_link(nxt->element, ptr));
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
      bucket* s = hash_table.get_bucket(k);
      link l = s->load();
      if (is_empty(l.next)) return {};
      if (KeyEqual{}(l.element.first, k)) return l.element.second;
      return epoch::with_epoch([&] () -> std::optional<V> {
        link l = s->load();
	if (is_empty(l.next)) return {};
	if (KeyEqual{}(l.element.first, k)) return l.element.second;
	return find_in_list(l.next, k);});
    }

    bool insert(const K& k, const V& v) {
      bucket* s = hash_table.get_bucket(k);
      __builtin_prefetch (s);
      return epoch::with_epoch([&] {
	long cnt = 0;
	while (true) {
	  link l = s->load();
	  //std::cout << "s: " << list_length(l) << std::endl;
	  //if (!s->check_ok()) std::cout << "bad check in insert" << std::endl;
	  if (is_empty(l.next)) {
	    if (s->cas(l, link(std::pair(k,v), nullptr))) return true;
	  } else {
	    if (KeyEqual{}(l.element.first, k)) return false;
	    if (find_in_list(l.next, k).has_value()) return false;
	    link* new_head = new_link(l.element, l.next);
	    if (s->cas(l, link(KV(k,v), new_head))) {
	      //std::cout << "e: " << list_length(s->load()) << ", " << s->load().next << ", " << is_empty(s->load().next) <<std::endl;
	      return true;
	    }
	    epoch::Delete(new_head);
	  }
	  if (cnt++ > 1000000) {std::cout << "insert infinite loop?" << std::endl; abort();} 
	}});
    }

    bool remove(const K& k) {
      bucket* s = hash_table.get_bucket(k);
      __builtin_prefetch (s);
      return epoch::with_epoch([&] {
	long cnt = 0;
	while (true) {
	  link l = s->load();
	  if (is_empty(l.next)) return false;
	  if (KeyEqual{}(l.element.first, k)) {
	    if (l.next == nullptr) {
	      if (s->cas(l, link()))
		return true;
	    } else {
	      if (s->cas(l, link(l.next->element, l.next->next))) {
		epoch::Retire(l.next);
		return true;
	      }
	    }
	  } else {
	    //if (is_empty(l.next)) {std::cout << "empty nxt??" << std::endl; abort();}
	    auto [cnt, new_head] = remove_from_list(l.next, k);
	    if (cnt == 0) return false;
	    if (s->cas(l, link(l.element, new_head))) {
	      retire_list(l.next, cnt);
	      return true;
	    }
	    retire_list(new_head, cnt - 1);
	  }
	  if (cnt++ > 1000000) {std::cout << "remove infinite loop?" << std::endl; abort();} 
	}});
    }

    long size() {
      return parlay::reduce(parlay::map(hash_table.table, [&] (bucket& x) {
							    return list_length(x.load());}));
    }

  };

} // namespace parlay
#endif //PARLAYHASH_H_
