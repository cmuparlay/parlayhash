#ifndef PARLAY_UNORDERED_MAP_
#define PARLAY_UNORDERED_MAP_

#define USE_SET

#include <functional>
#include <optional>
#include "parlay_hash.h"
#include <parlay/sequence.h>
#include <utils/epoch.h>

namespace parlay {

  template <typename K_, typename V_, class Hash = std::hash<K_>, class KeyEqual = std::equal_to<K_>>
  struct IndirectMapEntry {
    using K = K_;
    using V = V_;
    using Data = std::pair<K, V>;
    using Key = std::pair<const K*,size_t>;
    static constexpr bool Direct = false;
  private:
    Data* ptr;
    static Data* tagged_ptr(const Key& k, const V& v) {
      Data* x = epoch::New<Data>(*k.first, v);
      return (Data*) (((k.second >> 48) << 48) | ((size_t) x));
    }
    Data* get_ptr() const {
      return (Data*) (((size_t) ptr) & ((1ul << 48) - 1)); }
  public:
    static unsigned long hash(const Key& k) {return k.second;}
    bool equal(const Key& k) const {
      return (((k.second >> 48) == (((size_t) ptr) >> 48)) &&
	      KeyEqual{}(get_ptr()->first, *k.first)); }
    void retire() { epoch::Retire(get_ptr()); }
    V& get_value() const { return get_ptr()->second;}
    Key get_key() const { return make_key(get_ptr()->first);}
    Data get_entry() const { return *get_ptr();}
    static Key make_key(const K& key) { return Key(&key, Hash{}(key));}
    IndirectMapEntry(const Key& k, const V& v) : ptr(tagged_ptr(k, v)) {}
    IndirectMapEntry() {}
  };

  // not used :: work in progress
  template <typename K_, typename V_, class Hash = std::hash<K_>, class KeyEqual = std::equal_to<K_>>
  struct DirectMapEntry_ {
    using K = K_;
    using V = V_;
    using Key = K;
    using Data = std::pair<K, V>;
    static const bool Direct = true;
  private:
    using Bytes = std::array<char,sizeof(Data)>;
    Bytes data;
    Data* get_data() const {return (Data*) &data;}
  public:
    static unsigned long hash(const Key& k) {return Hash{}(k);}
    bool equal(const Key& k) const {
      return KeyEqual{}(get_data()->first, k); }
    void retire() {
      if constexpr (std::is_trivially_destructible_v<Data>);
      else epoch::Retire(epoch::New<Data>(*get_data()));
    }
    static Key make_key(const K& k) {return k;}
    const V& get_value() const {return get_data()->second;}
    const K& get_key() const {return get_data()->first;}
    Data get_entry() const { return *get_data();} 
    DirectMapEntry_(const Key& k, const V& v) {
      Data x(k,v);
      data = *((Bytes*) &x);
    }
    DirectMapEntry_() {}
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
    const V& get_value() const {return data.second;}
    const K& get_key() const {return data.first;}
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
    auto Find(const K& k, const F& f = get_value)
      -> std::optional<typename std::result_of<F(Entry)>::type>
    { return m.Find(Entry::make_key(k), f); }

    template <typename F = decltype(get_value)>
    auto Insert(const K& key, const V& value, const F& f = get_value)
      -> std::optional<typename std::result_of<F(Entry)>::type> 
    {
      auto x = Entry::make_key(key);
      return m.Insert(x, [&] {return Entry(x, value);}, f);
    }

    template <typename F = decltype(get_value)>
    auto Remove(const K& k, const F& f = get_value) 
      -> std::optional<typename std::result_of<F(Entry)>::type>
    { return m.Remove(Entry::make_key(k), f); }

    iterator find(const K& k) { return m.find(k); }

    std::pair<iterator,bool> insert(const value_type& entry) {
      return m.insert(Entry(entry.first, entry.second)); }

    iterator erase(iterator pos) { return m.erase(pos); }
    size_t erase(const K& k) { return m.erase(k); }

  };
  
  template <typename K, typename V, class Hash = std::hash<K>, class KeyEqual = std::equal_to<K>>
  using parlay_unordered_map = std::conditional_t<std::is_trivially_copyable_v<K> && std::is_trivially_copyable_v<V>,
						  unordered_map_<DirectMapEntry<K, V, Hash, KeyEqual>>,
						  unordered_map_<IndirectMapEntry<K, V, Hash, KeyEqual>>>;

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
    Key get_key() const { return make_key(*get_ptr());}
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
    Key get_key() const { return data;}
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

    bool Find(const K& k) {
      return m.Find(Entry::make_key(k), true_f).has_value(); }
    
    bool Insert(const K& key) {
      auto x = Entry::make_key(key);
      return !m.Insert(x, [&] {return Entry(x);}, true_f).has_value(); }

    bool Remove(const K& k) {
      return m.Remove(Entry::make_key(k), true_f).has_value(); }

    iterator erase(iterator pos) { return m.erase(pos); }

    std::pair<iterator,bool> insert(const value_type& entry) {
      return m.insert(Entry(entry));
    }

    iterator find(const K& k) { return m.find(k); }

  };

  template <typename K, class Hash = std::hash<K>, class KeyEqual = std::equal_to<K>>
  using parlay_unordered_set = std::conditional_t<std::is_trivially_copyable_v<K>,
					   unordered_set_<DirectSetEntry<K, Hash, KeyEqual>>,
					   unordered_set_<IndirectSetEntry<K, Hash, KeyEqual>>>;
}  // namespace parlay
#endif  // PARLAY_BIGATOMIC_HASH_LIST
