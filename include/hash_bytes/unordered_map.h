// MIT license (https://opensource.org/license/mit/)
// Initial Author: Guy Blelloch
// Developed as part of the flock library
// 

#ifndef PARLAYHASH_H_
#define PARLAYHASH_H_

#include <atomic>
#include <optional>
#include <parlay/primitives.h>
#include <parlay/sequence.h>
#include "lock.h"

namespace parlay {
  
  template <typename K,
	    typename V,
	    class Hash = std::hash<K>,
	    class KeyEqual = std::equal_to<K>>
  struct unordered_map {
    using KV = std::pair<K,V>;
    using tag = unsigned char;
    static constexpr tag empty = 128;
    static constexpr tag pad = 64;

    long hash_to_shard(size_t hash) {
      return hash & (num_shards-1);
    }

    struct alignas(64) header {
      std::atomic<long> table_version;
      long count;
      long size;
      tag* tags;
      KV* data;
      //size_t pad[3];
      //std::atomic<int> lock;
	
      header(tag* tags, KV* data, long size)
	: table_version(0), count(0), tags(tags), data(data), size(size) {} //, lock(-1) {}
    
      std::pair<long,tag> split_hash(size_t hash) {
	return std::pair((hash >> 7) & (size -1), hash & 127);
      }

      std::tuple<bool, bool,long>
	find_location_snapshot(long version, char* buffer, long h1, long h2, K k) {
	long i = h1;
	if (version & 1) return std::tuple(false,false,0);
	while (tags[i] != empty) {
	  if (tags[i] == h2) {
	    memcpy(buffer, &data[i], sizeof(KV));
	    if (version != table_version) return std::tuple(false,false,0);
	    if (KeyEqual{}(*((K*) buffer), k)) return std::tuple(true,true,i);
	  }
	  i++;
	}
	if (version != table_version) std::tuple(false,false,0);
	return std::tuple(true,false,i);
      }

      long find_location(long h1, long h2, K k) {
	long i = h1;
	while (tags[i] != empty) {
	  if (tags[i] == h2 && KeyEqual{}(data[i].first, k)) break;
	  i++;
	  //if (i == (size + pad)) abort();
	}
	return i;
      }
      
      std::optional<V> find(size_t hash, const K& k) {
	auto [h1, h2] = split_hash(hash);
	long i;
	long version;
	char buffer[sizeof(KV)];
	while (true) {
	  version = table_version.load();
	  auto [ok, found, i] = find_location_snapshot(version, buffer, h1, h2, k);
	  if (ok) 
	    if (found) return {};
	    else return ((KV*) buffer)->second;	
	} 
      }

      // bool try_lock(long version) {
      // 	int x = -1;
      // 	if (lock.load() != x || table_version.load() != version || !lock.compare_exchange_strong(x, (int) parlay::worker_id()))
      // 	  return false;
      // 	if (table_version.load() == version) {
      // 	  table_version++;
      // 	  return true;
      // 	}
      // 	lock.store(-1);
      // 	return false;
      // }

      // void unlock(long version) {
      // 	table_version.store(version+2);
      // 	lock.store(-1);
      // }

      bool try_lock(long version) {
      	return (!(version & 1) &&
      		table_version.compare_exchange_strong(version, version+1));
      	}

      void unlock(long version) {
      	table_version.store(version+2, std::memory_order_relaxed);
      }
	
      bool insert(size_t hash, const K& k, const V& v) {
	//std::cout << k << std::endl;
	auto [h1, h2] = split_hash(hash);
	char buffer[sizeof(KV)];
	long cnt = 0;
	long delay = 100;
	while (true) {
	  long version = table_version.load();
	  auto [ok, found, i] = find_location_snapshot(version, buffer, h1, h2, k);
	  if (ok && found) return false;
	  __builtin_prefetch (data + i);
	  if (get_locks().try_lock((long) data, [=] {
	         if (version != table_version.load()) return false;
		 table_version = version + 1;
		 tags[i] = h2;
		 data[i] = KV{k,v};
		 count++;
		 table_version.store(version + 2, std::memory_order_relaxed);
		 return true;}))
	    return true;
	  //for (volatile int i=0; i < delay; i++);
	  delay = std::min(20000l, 2*delay);
	}
      }
	    
      bool remove(size_t hash, const K& k) {
	auto [h1, h2] = split_hash(hash);
	char buffer[sizeof(KV)];
	long delay = 100;
	while (true) {
	  long version = table_version.load();
	  auto [ok, found, i] = find_location_snapshot(version, buffer, h1, h2, k);
	  if (ok && !found) return false;
	  //__builtin_prefetch (data + i);
	  if (get_locks().try_lock((long) data, [=] {
   	         if (version != table_version.load()) return false;
		 table_version = version + 1;
		 tags[i] = empty;
		 backfill(i);
		 count--;
		 table_version.store(version + 2, std::memory_order_relaxed);
		 return true;}))
	    return true;
	  //for (volatile int i=0; i < delay; i++);
	  delay = std::min(20000l, 2*delay);
	}
      }

      void backfill(long i) {
	long j = i+1;
	while (true) {
	  if (tags[j] == empty) return;
	  if (split_hash(Hash{}(data[j].first)).first <= i) {
	    data[i] = data[j];
	    std::swap(tags[i],tags[j]);
	    backfill(j);
	    return;
	  }
	  j++;
	  //if (j == (size + pad)) {std::cout << "backfill" << std::endl; abort();}
	}
      }
    };

    parlay::sequence<tag> all_tags;
    parlay::sequence<KV> all_data;
    parlay::sequence<header> headers;
    int per_shard_bits;
    size_t num_shards;
    
    unordered_map(long n) {
      int shard_bits = parlay::log2_up(parlay::num_workers()) + 5;
      num_shards = 1ul << shard_bits;
      size_t m = n / num_shards;
      int bits = 1 + parlay::log2_up(m);
      size_t per_shard_size = (1ul << bits) + pad;
      per_shard_bits = bits + 7;
      all_data = parlay::sequence<KV>(num_shards * per_shard_size);
      all_tags = parlay::sequence<tag>(num_shards * per_shard_size, empty);
      headers = parlay::tabulate(num_shards, [&] (long i) {
	         return header(all_tags.begin() + i * per_shard_size,
			       all_data.begin() + i * per_shard_size,
			       per_shard_size - pad);});
    }

    ~unordered_map() {}

    std::pair<size_t,size_t> get_hashes(const K& k) {
      size_t hash = Hash{}(k);
      return std::pair((hash >> per_shard_bits) & (num_shards-1ul), hash);
    }

    std::optional<V> find(const K& k) {
      auto [shard_id, shard_hash] = get_hashes(k);
      return headers[shard_id].find(shard_hash, k);
    }

    bool insert(const K& k, const V& v) {
      auto [shard_id, shard_hash] = get_hashes(k);
      return headers[shard_id].insert(shard_hash, k, v);
    }
  
    bool remove(const K& k) {
      auto [shard_id, shard_hash] = get_hashes(k);
      return headers[shard_id].remove(shard_hash,k);
    }

    long size() {
      long result = 0;
      for (int i=0; i < num_shards; i++) {
	result += headers[i].count;
      }
      return result;
    }

  };

} // namespace parlay
#endif //PARLAYHASH_H_
