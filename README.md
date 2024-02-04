# ParlayHash :

A Header-Only Concurrent Hash Map.  It is growable and is designed to
scale well to hundreds of threads and work reasonably well under high
contention.

The simplest way to use the library is to copy the [include](include) directory into your code directory
and then include the following in your code:

```
#include "include/parlay_hash/unordered_map.h"
```

Here are some comparisons of timings and memory usage to the
most widely used open-source concurrent hash tables.  These numbers are
averages (geometric means) over a variety of work loads.  The workloads and details on
experiments are described below.

| Hash Map | Memory | 1 thread | 16 threads | 128 threads | 128 insert | 
| - | - | - | - | - | - | 
| - | bytes/elt | Mops/sec | Mops/sec | Mops/sec | Mops/sec | 
| [parlay_hash](./README.md) | [26.3](timings/parlay_hash_1) | [21.4](timings/parlay_hash_1) | [214](timings/parlay_hash_16) | [1130](timings/parlay_hash_128) | [370](timings/parlay_hash_128) | 
| [parlay_hash_2x](./README.md) | [41.0](timings/parlay_hash_2x_1) | [24.4](timings/parlay_hash_2x_1) | [251](timings/parlay_hash_2x_16) | [1259](timings/parlay_hash_2x_128) | [393](timings/parlay_hash_2x_128) | 
| [tbb_hash](https://spec.oneapi.io/versions/latest/elements/oneTBB/source/containers/concurrent_unordered_map_cls.html) | --- | [13.2](timings/tbb_hash_1) | [71](timings/tbb_hash_16) | [54](timings/tbb_hash_128) | [23](timings/tbb_hash_128) | 
| [libcuckoo](https://github.com/efficient/libcuckoo) | [43.6](timings/libcuckoo_1) | [14.2](timings/libcuckoo_1) | [58](timings/libcuckoo_16) | [29](timings/libcuckoo_128) | [299](timings/libcuckoo_128) | 
| [folly_hash](https://github.com/facebook/folly/blob/main/folly/concurrency/ConcurrentHashMap.h) | [91.9](timings/folly_hash_1) | [12.2](timings/folly_hash_1) | [107](timings/folly_hash_16) | [157](timings/folly_hash_128) | [237](timings/folly_hash_128) | 
| [folly_sharded](other/folly_sharded/unordered_map.h) | [34.5](timings/folly_sharded_1) | [19.4](timings/folly_sharded_1) | [84](timings/folly_sharded_16) | [116](timings/folly_sharded_128) | [329](timings/folly_sharded_128) | 
| [boost_hash](https://www.boost.org/doc/libs/1_83_0/libs/unordered/doc/html/unordered.html#concurrent) | [37.9](timings/boost_hash_1) | [25.3](timings/boost_hash_1) | [115](timings/boost_hash_16) | [58](timings/boost_hash_128) | [30](timings/boost_hash_128) | 
| [parallel_hashmap](https://github.com/greg7mdp/parallel-hashmap) | [36.0](timings/parallel_hashmap_1) | [22.0](timings/parallel_hashmap_1) | [85](timings/parallel_hashmap_16) | [112](timings/parallel_hashmap_128) | [185](timings/parallel_hashmap_128) | 
| [seq_hash](https://github.com/Thermadiag/seq/blob/main/docs/concurrent_map.md) | [33.4](timings/seq_hash_1) | [23.5](timings/seq_hash_1) | [125](timings/seq_hash_16) | [105](timings/seq_hash_128) | [289](timings/seq_hash_128) | 
| [abseil (sequential)](https://abseil.io/docs/cpp/guides/container) | [36.0](timings/abseil_1) | [40.1](timings/abseil_1) |  --- | --- | --- |
| [folly_F14 (sequential)](https://engineering.fb.com/2019/04/25/developer-tools/f14/) | [24.7](timings/folly_F14_1) | [28.9](timings/folly_F14_1) |  --- | --- | --- |
| [std_hash (sequential)](https://en.cppreference.com/w/cpp/container/unordered_map) | [44.7](timings/std_hash_1) | [15.0](timings/std_hash_1) |  --- | --- | --- |

All performance numbers are in millions of operations per second
(Mops/sec or mops).  All experiments were run on AWS EC2 c6i
instances, which are Intel Xeon Ice Lake processors (more details
below).
The `threads` columns are for a mix of insert/delete/find operations on different numbers of threads.
The `insert`  column is for inserting 10M unique keys on 128 
threads with the table initialized to the correct final size.
The `memory` column is the memory usage per entry (in bytes) of the hash table

Details across the workloads can be found by clicking on the numbers.
At 128 threads `parlay_hash` is faster across all workloads compared
to all other hash tables listed.  Most of the others are particularly
bad under high contention.  The exception is `folly_hash`, which does
reasonably well under contention, but istead is bad under update heavy
workloads.  It also uses a lot of memory.
`parlay_hash_2x` is the same as `parlay_hash` but with the table
initialized to size 2n instead of n.

## Interface

The library supports the following interface for any copyable key type `K` and value type `V`.

- `parlay::parlay_unordered_map<K,V,Hash=std::hash<K>,Equal=std::equal_to<K>>(long n, bool cleanup=false)` :
constructor for map of initial size n.  If `cleanup` is set, all memory pools and scheduler threads will
be cleaned up on destruction, otherwise they can be shared among hash maps.

- `Find(const K&) -> std::optional<V>` : If the key is in the map, returns the value associated
  with it, otherwise returns std::nullopt.

- `Find(const K&, (const V&) -> T) -> std::optional<T>` : Same as
  `Find(k)` but, if found, applies the function to the value and returns the result.
  Can be useful if `V` is large and only a summary is needed.

- `Insert(const K&, const V&) -> std::optional<V>` : If the key is in
the map, returns the value without doing an update, otherwise inserts the key with the
given value and returns std::nullopt.

- `Insert(const K&, const V&, (const V&) -> T) -> std::optional<T>` : Same as `Insert(k,v)` but, if
already in the table, applies the function to value and returns the result.

- `Remove(const K&) -> std::optional<V>` : If the key is in the map, removes the
  key-value and returns the value, otherwise it returns std::nullopt.

- `Remove(const K&, (const V&) -> T) -> std::optional<T>` : Same as `Remove(k)` but, if removed,
applies the function to the removed value and returns the result.

- `Upsert(const K&, const V&) -> std::optional<V>` : If the key is in the map, updates
the value with given value and returns the old value, otherwise inserts the key value pair
and returns std::nullopt.

- `Upsert(const K&, (const std::optional<V>&) -> V)) -> std::optional<V>` : If the
key is in the map with an associated value v then it applies the function (second argument)
to `std::optional<V>(v)`, replaces the current value for the key with the
returned value, and returns the old value.  Otherwise it applies the
function to std::nullopt and inserts the key into the map with the
returned value, and returns std::nullopt.   For example: `Upsert(k, [&] (auto v) {return (v.has_value()) ? *v + 1 : 1;})` will atomically increment the value by 1 if there, or set the value to 1 if not.

- `size() -> long` : Returns the number of elements in the map.
Runs in **parallel** and does work proportional to the
number of elements in the hash map.   Safe to run with other operations, but is
not linearizable with updates.  However it always
includes any elements that are in there from its invocation until its
response, and never includes an element that is removed before its
invocation or is inserted after its response.  This means, for
example, that if there are no concurrent updates, it returns the
correct size.  

- `for_each(std::pair<K,V> -> void) -> void` :
Applies the given function to each element in the map.  Has the same weakly linearizable properties as
size.

- `clear() -> void` : Clears all entries of the map.   It does not resize.

The type for keys (K) and values (V) must be copyable, and might be
copied by the hash map even when not being updated (e.g. when
another key in the same bucket is being updated).

A simple example can be found in [examples/example.cpp](examples/example.cpp)

The library supports growable hash maps, although if the proper size
is given on construction, no growing will be needed.  The number of
buckets increase by a constant factor when any bucket gets too large.
The copying is done incrementally by each update.

There is also a `parlay::parlay_unordered_set` that supports sets of keys.  It has a similar
interface.

## Benchmarks

Benchmarks for comparing performance to other hash maps can be found
in `benchmarks`.  With `cmake` the following can be used to compile and run
the benchmarks:

    git clone https://github.com/cmuparlay/parlayhash.git
    cd parlayhash
    mkdir build
    cd build
    cmake ..
    make -j
    cd benchmarks
    ./parlay_hash           // run the benchmark for our map
    ...

In addition to our hash map, the repository includes the following open source hash maps:
- ./tbb_hash            ([tbb concurrent hash map](https://spec.oneapi.io/versions/latest/elements/oneTBB/source/containers/concurrent_unordered_map_cls.html))
- ./libcuckoo           ([libcuckoo's cuckooohash_map](https://github.com/efficient/libcuckoo))
- ./folly_hash          ([folly's ConcurrentHashMap](https://github.com/facebook/folly/blob/main/folly/concurrency/ConcurrentHashMap.h))
- ./boost_hash          ([boost's concurrent_flat_map](https://www.boost.org/doc/libs/1_83_0/libs/unordered/doc/html/unordered.html#concurrent))
- ./parallel_hashmap    ([parallel hashmap](https://github.com/greg7mdp/parallel-hashmap)) **
- ./seq_hash    ([seq's concurrent hashmap](https://github.com/Thermadiag/seq/blob/main/docs/concurrent_map.md)) **
- ./folly_sharded       (our own sharded version using folly's efficient [non-concurrent F14map](https://github.com/facebook/folly/blob/main/folly/container/F14Map.h)) **
- ./std_sharded         (our own sharded version of std::unordered_map) **

<!--- 
- ./growt               ([growt's concurrent hash map](https://github.com/TooBiased/growt))
--->

For some of these you need to have the relevant library installed
(e.g., boost, folly, abseil, tbb).  All of them support arbitrary
copyable key and value types when supplied hash and equality functions
for the keys.

The tables marked with ** are "semi" growable.  In particular they are all
sharded and to perform well one needs to select the right number of
shards, which depends on the expected size and number of threads.  For
the experiments given below we selected 2^14 shards unless the library
limited the number of shards to a smaller number, in which case we
picked the largest number.  We note this would be very wasteful for
small tables, requiring hundreds of thousands of bytes even for a
table with a single entry.

Adding another hash table simply requires adding a stub file `other/<myhash>/unordered_map.h`
(e.g., see [other/boost/hash/unordered_map.h](other/boost/hash/unordered_map.h))
and adding a line of the form:

    add_benchmark(<myhash> other <link_libraries> <compiler_options> <compiler_definitions>)

to [CMakeFile.txt](benchmarks/CMakeFiles.txt).

The benchmarks will run by default on the number of hardware threads
you have on your machine.

## Workloads

The experiments run a variety of workloads and report a geometric mean across the workloads.
The default workloads are the following:

- Table of long keys and long values : will run over two data sizes
(10K and 10M), three update percents (0%, 10% and 50%), and two
distributions (uniform and zipfian=.99).  This is a total of 12
workloads since all combinations are tried.  The updates are 50%
insertions (without replacement if already there) and 50% removes, the
rest of the operations are finds.  For example, the 50% update
workload will have 25% insertions, 25% removes, and 50% finds.
We note that zipfian .99 is what is suggested by the YCSB [Yahoo Cloud
Serving Benchmark](https://research.yahoo.com/news/yahoo-cloud-serving-benchmark) as a good model for the skew of real-world
data used in key value stores.

- Set of ints: will run over over 2 sizes (10K and 10M) with update
percent set 10% and zipfian set to zero.  This is to test how it does
and small entries.

- Table of strings for keys, and 4-tuples of longs for values.  The
keys are selected from a trigram distribution, so they have skew that
is meant to represents the skew of word probabilities in the English
Language.  The experiment runs over a single map size (about 1.2
Million entries) and three updated percents (0%, 10% and 50%).

In addition to reporting the performance in operations per second, it
reports the performance to fill the initial table using inserts.
It reports the geometric mean for the largest experiment across the
three types (i.e 10M for long-long and int, and 1.2M for strings).

Finally it reports the geometric mean of the number of bytes used per
element for the hash tables that use each of the three types
(long-long, int, string-4xlong).  This is total memory as measured by
jemalloc (i.e. difference in allocated memory from before the table is
created until after it is created and all n elements are inserted).
Note the perfect number (i.e., no wasted memory) would be
(16 x 4 x 56)^(1/3) = 15.3 (long-long = 16 bytes, int = 4 bytes
string-4xlong = 24 + 4*8 = 56 bytes).  Hence, for example, 30 would
indicate approximately a factor of 2x overhead.

## Timings

The timings reported in the table are for an AWS EC2 c6i.large
instance for one thread, an AWS EC2 c6i.4xlarge instance for 16
threads, and a c6i.32xlarge instance for 128 threads.  These all use
Intel Xeon Ice Lake chips, and are 2 way hyperthreaded (e.g. the
c6i.32xlarge has 64 cores, corresponding to 128 hyperthreads).  All
timings are on the Ubuntu (linux) OS.  The c6i.32xlarge has two nodes
so we use "numactl -i all" to distribute the memory across the two
nodes for all experiments.  This slightly improves average
performance, but more importantly makes the performance more stable.
We set hugepages to "always", which reduces the number of TLB
(translation lookaside buffer) misses for both ours and all the other
hash tables.  In particular on Ubuntu we use: `echo always >
/sys/kernel/mm/transparent_hugepage/enabled`.  This needs to be done
in privileged mode (i.e., using `sudo`).  It improves performance on
average across workloads by about ten percent, with larger gains on
larger sizes.

## Options

Options include:

    -n <size>  : just this size
    -u <update percent>   : just this percent
    -z <zipfian parameter>  : just this zipfian parameter
    -grow : starts map at size 1 instead of size n
    -verbose : prints out some extra information
    -t <time in seconds>  : length of each trial, default = 1
    -r <num rounds>  : number of rounds for each size/update-percent/zipfian, default = 2
    -p <num threads> 

## Code Dependencies

The file [include/parlay_hash/unordered_map.h](include/parylay_hash/unordered_map.h) is mostly self contained.
The only non C++ standard library files that it uses are the following:
- [include/utils/epoch.h](include/utils/epoch.h), which is an implementation of epoch-based safe memory reclamation.   It supports the functions `New<T>(...args)` and `Retire(T* ptr)`, which correspond to `new` and `delete`.   The retire, however, delays destruction until it is safe to do so (i.e., when no operation that was running at the time of the retire is still running).
- [include/utils/lock.h](include/utils/lock.h), which is a simple implementation of shared locks.  It is only used if you use the lock-based version of the parlay_hash.  The implementation has an array with a fixed number of locks (currently 65K), and a location is hashed to one of the locks in the array.   Each lock is a simple spin lock.    This file has no dependencies beyond the C++ standard library.

ParlayHash optionally uses
[parlaylib](https://github.com/cmuparlay/parlaylib), by defining the
variable `USE_PARLAY`.  This will allow certain operations to run in
parallel.  In particular the array of buckets is initialized in
parallel, and the `size` and `entries` functions run in parallel.  The
parlaylib files are included in the repository so it need not be
installed.  Note that parlaylib will start up threads as needed to run
certain operations in parallel.  Once no longer needed, these will go
to sleep but will still be around.

The other implementations (e.g. tbb, folly, ...) require the relevant libraries, but do not require `parlaylib` themselves.   However, our benchmarking harness uses `parlaylib` to run the benchmarks for all implementations.

## Code Organization

The directory is organized as follows

```
include - all our hash map code and all dependencies
other - all the other implementations
benchmark - the code for running benchmarks both on our code and other code
examples - a couple of simple examples
timings - some timing results
```

## Acknowledgments

We would like to thank Google for their support in developing this code.
