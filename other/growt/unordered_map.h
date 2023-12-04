#include <atomic>
#include <random>
#include <thread>

#define USE_HANDLE 1

#include "allocator/alignedallocator.hpp"
#include "data-structures/hash_table_mods.hpp"
#include "utils/hash/murmur2_hash.hpp"

#include "data-structures/table_config.hpp"
template <typename K,
	  typename V,
	  class Hash = std::hash<K>,
	  class KeyEqual = std::equal_to<K>>
struct unordered_map {

  using K_Type = K;
  using V_Type = V;
  using hasher_type    = Hash; //utils_tm::hash_tm::murmur2_hash;
  using allocator_type = growt::AlignedAllocator<>;
  
  using table_type =
    typename growt::table_config<K_Type, V_Type, hasher_type, allocator_type,
				 hmod::growable, hmod::deletion>::table_type;

  using handle_type = typename table_type::handle_type;

  table_type table;

  std::optional<V> find(handle_type& my_handle, const K& k) {
    auto r = my_handle.find(k);
    if (r == my_handle.end()) return std::optional<V>();
    else return (*r).second;
  }

  bool insert(handle_type& my_handle, const K& k, const V& v) {
    auto x = my_handle.insert(k, v);
    return x.second;
  }

  bool remove(handle_type& my_handle, const K& k) {
    return my_handle.erase(k);
  }

  handle_type get_handle() {
    return table.get_handle();
  }

  unordered_map(size_t n) : table(table_type(n)) {}

  ~unordered_map() {}

  long size() {
    auto my_handle = get_handle();
    long count = 0;
    for (auto x : my_handle) count++;
    return count;}
};

