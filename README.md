# ParlayHash :
A Header-Only Scalable Concurrent Hash Map.

A growable concurrent hash map supporting **wait-free finds** and mostly **lock-free
updates** (some locks are taken when growing, but when not growing all updates are lock free).
It is designed to scale well to  hundreds of threads and work reasonably well under high contention.

The simplest way to use the library is to copy the [include](include) directory into your code directory
and then include the following in your code:

```
#include "include/parlay_hash/unordered_map.h"
```

## Interface

The library supports the following interface for any copyable key type `K` and value type `V`.

- `parlay::unordered_map<K,V,Hash=std::hash<K>,Equal=std::equal_to<K>>(long n, bool cleanup=false)` :
constructor for map of initial size n.  If `cleanup` is set, all memory pools and scheduler threads will
be cleaned up on destruction, otherwise they can be shared among hash maps.

- `find(const K&) -> std::optional<V>` : If the key is in the map, returns the value associated
  with it, otherwise returns std::nullopt.

- `insert(const K&, const V&) -> bool` : If the key is in the map, returns false, otherwise inserts the key
with the given value and returns true.

- `remove(const K&) -> bool` : If the key is in the map, removes the
  key-value and returns true, otherwise it returns false.

- `upsert(const K&, (const std::optional<V>&) -> V)) -> bool` : If the
key is in the map with an associated value v then it applies the function (second argument)
to `std::optional<V>(v)`, replaces the current value for the key with the
returned value, and returns false.  Otherwise it applies the
function to std::nullopt and inserts the key into the map with the
returned value, and returns true.   For example using: `[&] (auto x) {return v;}` will just set
the given key to have value v whether it was in there or not. 

- `size() -> long` : Returns the number of elements in the map.
Runs in **parallel** and does work proportional to the
number of elements in the hash map.   Safe to run with other operations, but is
not linearizable with updates.  However it always
includes any elements that are in there from its invocation until its
response, and never includes an element that is removed before its
invocation or is inserted after its response.  This means, for
example, that if there are no concurrent updates, it returns the
correct size.  

- `entries() -> parlay::sequence<std::pair<K,V>>` : Returns a [parlay]
(https://github.com/cmuparlay/parlaylib) sequence
containing all the entries of the map as key-value pairs.  Runs in
**parallel** and takes work proportional to the number of elements in
the hash map.  Safe to run with other operations, but is not
linearizable with updates.  Its concurrency semantics are the same as
for `size`.

<!---
The type for keys (K) and values (V) must be copyable, and might be
copied by the hash map even when not being updated (e.g. when
another key in the same bucket is being updated).
--->

A simple example can be found in [examples/example.cpp](examples/example.cpp)

The library supports growable hash maps, although if the proper size
is given on construction, no growing will be needed.  The number of
buckets increase by a constant factor when any bucket gets too large.
The copying is done incrementally by each update, allowing for a
mostly lock-free implementation.  Queries (finds) are still wait-free,
but updates can take a fine-grained lock (on a block of buckets) when
the hash map is growing.  Also allocation of a new **uninitialized
array** for the buckets at the start of a grow cycle takes a lock to
avoid multiple allocations, and since the allocator will most likely
take a lock anyway for large arrays.

By default the implementations are lock free (or mostly lock free when
growing).  However, we also support locked-based versions by defining
`USE_LOCKS`.  In the locked-based version, queries (finds) will still
be wait free, but updates take locks.  One advantage of the lock-based
version is that the function passed to `upsert` will be run in
isolation (i.e., mutually exclusive of any other invocation of the
function by an upsert on the same key) and just once.  With the
lock-free version the function could be run multiple times
concurrently, although the value of only one will be used.


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
- ./growt               ([growt's concurrent hash map](https://github.com/TooBiased/growt))
- ./folly_hash          ([folly's ConcurrentHashMap](https://github.com/facebook/folly/blob/main/folly/concurrency/ConcurrentHashMap.h))
- ./boost_hash          ([boost's concurrent_flat_map](https://www.boost.org/doc/libs/1_83_0/libs/unordered/doc/html/unordered.html#concurrent))
- ./parallel_hashmap    ([parallel hashmap](https://github.com/greg7mdp/parallel-hashmap))
- ./folly_sharded       (our own sharded version using folly's efficient [non-concurrent F14map](https://github.com/facebook/folly/blob/main/folly/container/F14Map.h))
- ./abseil_sharded      (our own sharded version using folly's efficient [non-concurrent flat_hash_map](https://abseil.io/docs/cpp/guides/container))
- ./std_sharded         (our own sharded version of std::unordered_map)

For some of these you need to have the relevant library installed
(e.g., boost, folly, abseil, tbb).  All of the hash maps except the
sharded versions are designed to grow.  All of them except `growt`
support arbitrary copyable key and value types when supplied hash and
equality functions for the keys.

Adding another hash table simply requires adding a stub file `other/<myhash>/unordered_map.h`
(e.g., see [other/boost/hash/unordered_map.h](other/boost/hash/unordered_map.h))
and adding a line of the form:

    add_benchmark(<myhash> other <link_libraries> <compiler_options> <compiler_definitions>)

to [CMakeFile.txt](benchmarks/CMakeFiles.txt).

The benchmarks will run by default on the number of hardware threads
you have on your machine.  They will run over two data sizes (100K and
10M), two update percents (5% and 50%), and two distributions (uniform
and zipfian=.99).  This is a total of 8 workloads since all
combinations are tried.  The updates are 50% insertions (without
replacement if already there) and 50% removes, the rest of the
operations are finds.  For example, the 50% update workload will have
25% insertions, 25% removes, and 50% finds.  The key-value pairs
consist of two longs.  The experiment is set up so 1/2 the insertions
and 1/2 the removes are successful on average.

Performance is reported in millions of operations-per-second (mops) for
each combination.  The geometric mean over all combinations is also reported.
Options include:

    -n <size>  : just this size
    -u <update percent>   : just this percent
    -z <zipfian parameter>  : just this zipfian parameter
    -grow : starts map at size 1 instead of size n
    -verbose : prints out some extra information
    -t <time in seconds>  : length of each trial, default = 1
    -r <num rounds>  : number of rounds for each size/update-percent/zipfian, default = 2
    -p <num threads> 

## Timings

Here are some timings on a AWS EC2 c6i.metal instance.  This machine
has two Intel Xeon Ice Lake chips with 32 cores each.  Each core is 2-way hyperthreaded, for a
total of 128 threads.  Each number reports the geometric mean of mops over the eight
workloads mentioned above (two sizes x two update rates x two
distributions).  For our hash map, we show both the times for
the locked (lock) and lock free (lf) versions.

Columns 2 through 4 correspond to 1 thread, 16 threads (8 cores) and 128 threads (64 cores) when the hash map is initialized
to the correct size.
The fifth column is the same but when the hash map is initialized with size 1 (i.e., it first grows to the full size and then the timings start).   This is meant to test if the hash map grows effectively, which all the growing maps do.
The sixth column is for inserting 10M unique keys on 128 threads when the hash map starts with size 1 (i.e., it includes the time for growing the hash map multiple times).

<!---
| hash_nogrow lf | 17.2 | 650 | --- | --- |
| hash_nogrow lock | 17.4 | 681 | --- | --- |
| hash_grow lf | 13.4 | 592 | 577 | 103 |
| hash_grow lock | 13.2 | 622 | 583 | 75 |
--->

| Hash Map | 1 thread | 16 threads | 128 threads | 128 grown | 128 insert |
| - | - | - | - | - | - |
| parlay_hash lf | 15.9 | 162 | 651 | 631 | 112 |
| parlay_hash lock | 16.1 | 156 | 692 | 679 | 99 |
| tbb_hash | 9.3 | 62.4 | 64.6 | 61.4 | 23 |
| libcuckoo | 11.5 | 50.5 | 33.1 | 33.9 | 6.3 |
| growt | 7.2 | 40.8 | 156 | 146 | 59 |
| folly_hash | 11.9 | 82.4 | failed | failed | 41 |
| boost_hash | 24.7 | 84.7 | 57.2 | 57.6 | 13.6 | 
| parallel_hashmap | 24.4 | 17.8 | 10.4 | 11.4 | 8 |
| folly_sharded | 16.5 | 76.9 | 125 |--- | --- |
| abseil (sequential) | 40.1 | --- | --- | --- | --- |
| std (sequential) | 13.2 | --- | --- | --- | --- |

Many of the other hash maps do badly on many threads under high contention.
For example, here are the full results for `libcuckoo` on 128 threads:

```
./libcuckoo,5%update,n=100000,p=128,z=0,grow=0,insert_mops=181,mops=536
./libcuckoo,5%update,n=10000000,p=128,z=0,grow=0,insert_mops=298,mops=385
./libcuckoo,50%update,n=100000,p=128,z=0,grow=0,insert_mops=188,mops=448
./libcuckoo,50%update,n=10000000,p=128,z=0,grow=0,insert_mops=296,mops=342
./libcuckoo,5%update,n=100000,p=128,z=0.99,grow=0,insert_mops=187,mops=2
./libcuckoo,5%update,n=10000000,p=128,z=0.99,grow=0,insert_mops=297,mops=2
./libcuckoo,50%update,n=100000,p=128,z=0.99,grow=0,insert_mops=185,mops=1
./libcuckoo,50%update,n=10000000,p=128,z=0.99,grow=0,insert_mops=296,mops=3
benchmark geometric mean of mops = 33.0592
initial insert geometric mean of mops = 234.931
```

The last four workloads are for z=.99 (zipfian parameter .99), and it does abysmally on these.  In comparison here is the full
result for `parlay_hash`:

```
./parlay_hash,5%update,n=100000,p=128,z=0,grow=0,insert_mops=83,mops=2024            
./parlay_hash,5%update,n=10000000,p=128,z=0,grow=0,insert_mops=226,mops=659          
./parlay_hash,50%update,n=100000,p=128,z=0,grow=0,insert_mops=123,mops=698           
./parlay_hash,50%update,n=10000000,p=128,z=0,grow=0,insert_mops=318,mops=470         
./parlay_hash,5%update,n=100000,p=128,z=0.99,grow=0,insert_mops=105,mops=1056        
./parlay_hash,5%update,n=10000000,p=128,z=0.99,grow=0,insert_mops=318,mops=969       
./parlay_hash,50%update,n=100000,p=128,z=0.99,grow=0,insert_mops=168,mops=216        
./parlay_hash,50%update,n=10000000,p=128,z=0.99,grow=0,insert_mops=317,mops=333      
benchmark geometric mean of mops = 651.735                                           
initial insert geometric mean of mops = 184.35
```

We note that zipfian .99 is what is suggested by the YCSB [Yahoo Cloud
Serving Benchmark](https://research.yahoo.com/news/yahoo-cloud-serving-benchmark) as a good model for the skew of real-world
data used in key value stores.


## Code Dependencies

Our hash map uses [parlaylib](https://github.com/cmuparlay/parlaylib)
for parallelism.  In particular the array of buckets is initialized in
parallel, and the `size` and `entries` functions run in parallel.  The
parlaylib files are included in the repository so it need not be
installed.
Note that parlaylib will start up threads as needed to run certain operations in parallel.   Once no longer needed, these will go to sleep but will still be around.

The file [include/parlay_hash/unordered_map.h](include/parylay_hash/unordered_map.h) is mostly self contained.
The only non C++ standard library files that it uses are the following:
- [include/utils/epoch.h](include/utils/epoch.h), which is an implementation of epoch-based safe memory reclamation.   It supports the functions `New<T>(...args)` and `Retire(T* ptr)`, which correspond to `new` and `delete`.   The retire, however, delays destruction until it is safe to do so (i.e., when no operation that was running at the time of the retire is still running).
- [include/utils/lock.h](include/utils/lock.h), which is a simple implementation of shared locks.  It is only used if you use the lock-based version of the parlay_hash.  The implementation has an array with a fixed number of locks (currently 65K), and a location is hashed to one of the locks in the array.   Each lock is a simple spin lock.    This file has no dependencies beyond the C++ standard library.
- Files from the [include/parlaylib](include/parlaylib) library.

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
