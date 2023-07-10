# parlayhash : A Header Only Fast Concurrent Hash Table.

Finds are constant time.  Updates are lock-free.

There are two versions:

- `include/hash_nogrow/unordered_map.h` : does not support growing the number of buckets.  It can grow arbitrarily large but each buckets will become large and the table will be slow.  Number of buckets is specified when table is constructed.   Updates are always lock-free.

- `include/hash_grow/unordered_map.h` : support increasing the number of buckets.  The number of buckets increase by a constant factor when any bucket gets too large.   The copying is done incrementally by each update, allowing for a lock-free implementation.

The two versions both support the following interface:

- `unordered_map<K,V,Hash=std::hash<K>,Equal=std::equal_to<K>>(n)` :
constructor for table of size n

- `find(const K&) -> std::optional<V>` : returns key if found, otherwise std::nullopt.

- `insert(const K&, const V&) -> bool` : if key not in the table it inserts the key
with the given value and returns true, otherwise does nothing and
returns false.

- `remove(const K&) -> bool` : if key is in the table it removes the entry
and returns true, otherwise it does nothing and returns false.

- `upsert(const K&, (const std::optional<V>&) -> V)) -> bool` : if
key is in the table with value v then it calls the function (second argument)
with std::optional<V>(v), replaces the current value with the
returned value, and returns false.  Otherwise it calls the
function with std::nullopt and inserts the key into the table with the
returned value, and returns true.

- `size() -> long` : returns the size of the table.  Not linearizable with
the other functions, and takes time proportional to the table size.

The type for keys (K) and values (V) must be copyable, and might be
copied by the hash_table even when not being updated (e.g. when
another key in the same bucket is being updated).

A simple example can be found in `examples/example.cpp`.

Benchmarks comparing to other hash tables can be found in `benchmarks`.

**Implementation**: Each bucket points to a structure (Node)
containing an array of entries.  Nodes come in varying sizes and on
update the node is copied.  When growing each bucket is copied to k
new buckets and the old bucket is marked as "forwarded".
