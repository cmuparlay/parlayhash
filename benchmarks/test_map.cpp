#include <string>
#include <iostream>
#include <chrono>
#include <tuple>

#include <parlay/primitives.h>
#include <parlay/random.h>
#include "zipfian.h"
#include "parse_command_line.h"

using K = unsigned long;
using V = unsigned long;
using namespace parlay;

#include "unordered_map.h"

// leave undefined if measuring througput since measuring latency will slow down throughput
//#define Latency 1

// growt requires handles, rest do not
#ifdef USE_HANDLE
#define HANDLE handle,
#else
#define HANDLE 
#endif

struct IntHash {
  using is_avalanching = void; // used by boost_hash to avoid secondary hashing
  std::size_t operator()(K const& k) const noexcept {
    auto x = k * UINT64_C(0xbf58476d1ce4e5b9); // linear transform
    return (x ^ (x >> 31));  // non-linear transform
  }
};

using map_type = unordered_map<K,V,IntHash>;

double geometric_mean(const parlay::sequence<double>& vals) {
  double product = 1;
  for (auto x : vals) product = product * x;
  return  pow(product, 1.0 / vals.size());
}

std::tuple<double,double>
test_loop(commandLine& C,
	  long n,   // num entries in map
	  long p,   // num threads
	  long rounds,  // num trials
	  double zipfian_param, // zipfian parameter [0:1) (0 is uniform, .99 is high skew)
	  int update_percent, // percent of operations that are either insert or delete (1/2 each)
	  bool upsert, // use upsert instead of insert
	  double trial_time, // time to run one trial
	  double latency_cutoff, // cutoff to measure percent below
	  bool verbose, // show some more info
	  bool warmup,  // run one warmup round
	  bool grow) {  // start with table of size 1
  // total samples used
  long m = 10 * n + 1000 * p;

  // generate 2*n unique numbers in random order
  // get rid of top bit since growt seems to fail if used (must use it itself)
  //auto x = parlay::delayed_tabulate(1.2* 2 * n,[&] (size_t i) {
  //		 return (K) (parlay::hash64(i) >> 1) ;}); 
  //auto y = parlay::random_shuffle(parlay::remove_duplicates(x));
  //auto a = parlay::tabulate(2 * n, [&] (size_t i) {return y[i];});

  // have to exlude key = 0 since growt does not seem to allow it
  auto a = parlay::random_shuffle(parlay::tabulate(2 * n, [] (K i) { return i + 1;}));

  // take m numbers from a in uniform or zipfian distribution
  parlay::sequence<K> b;
  if (zipfian_param != 0.0) { 
    Zipfian z(2 * n, zipfian_param);
    b = parlay::tabulate(m, [&] (int i) { return a[z(i)]; });
    a = parlay::random_shuffle(a);
  } else {
    b = parlay::tabulate(m, [&] (int i) {return a[parlay::hash64(i) % (2 * n)]; });
  }

  enum op_type : char {Find, Insert, Remove};

  // generate the operation types with update_percent updates
  // half the updates will be inserts and half removes
  auto op_types = parlay::tabulate(m, [&] (size_t i) -> op_type {
        auto h = parlay::hash64(m+i)%200;
        if (h < update_percent) return Insert; 
        else if (h < 2*update_percent) return Remove;
	else return Find; });

  parlay::sequence<double> insert_times;
  parlay::sequence<double> bench_times;
    
  for (int i = 0; i < rounds + warmup; i++) { {
    map_type map = grow ? map_type(1) : map_type(n);
    size_t np = n/p;
    size_t mp = m/p;
    
    // initialize the map with n distinct elements
    auto start_insert = std::chrono::system_clock::now();
#ifdef USE_HANDLE
    long block_size = 1 + (n-1) / p;
    parlay::parallel_for(0, p, [&] (size_t i) {
      auto handle = map.get_handle();
      long s = i * block_size;
      long e = std::min(s + block_size, n);
      for (int j = s; j < e; j++)
	map.insert(HANDLE a[j], 123); }, 1, true);
#else
    parlay::parallel_for(0, n, [&] (size_t i) {
	map.insert(a[i], 123); });
#endif
    if (map.size() != n)
      std::cout << "bad initial size = " << map.size() << std::endl;


    std::chrono::duration<double> insert_time = std::chrono::system_clock::now() - start_insert;
    double imops = n / insert_time.count() / 1e6;
    if (!warmup || i>0) 
      insert_times.push_back(imops);
    
    long initial_size = map.size();

    // keep track of some statistics, one entry per thread
    parlay::sequence<size_t> totals(p);
    parlay::sequence<long> addeds(p);
    parlay::sequence<long> removeds(p);
    parlay::sequence<long> query_counts(p);
    parlay::sequence<long> query_success_counts(p);
    parlay::sequence<long> update_success_counts(p);
    parlay::sequence<long> latency_counts(p);

    if (verbose) std::cout << "entries inserted" << std::endl;

    auto start = std::chrono::system_clock::now();
		   
    // start up p threads, each doing a sequence of operations
    parlay::parallel_for(0, p, [&] (size_t i) {
      int cnt = 0;
      size_t j = i*mp;
      size_t k = i*mp;
      size_t total = 0;
      long added = 0;
      long removed = 0;
      long query_count = 0;
      long query_success_count = 0;
      long update_success_count = 0;
      long latency_count = 0.0;
#ifdef USE_HANDLE
      auto handle = map.get_handle();
#endif
      
      while (true) {
	// every once in a while check if time is over
	if (cnt >= 100) {
	  cnt = 0;
	  auto current = std::chrono::system_clock::now();
	  std::chrono::duration<double> duration = current - start;
	  if (duration.count() > trial_time) {
	    totals[i] = total;
	    addeds[i] = added;
	    removeds[i] = removed;
	    query_counts[i] = query_count;
	    query_success_counts[i] = query_success_count;
	    update_success_counts[i] = update_success_count;
	    latency_counts[i] = latency_count;
	    return;
	  }
	}

	// do one of find, insert, or remove
	if (op_types[k] == Find) {
	  query_count++;
#ifdef Latency
	  auto start_op_time = std::chrono::system_clock::now();
	  query_success_count += map.find(HANDLE b[j]).has_value();
	  auto current = std::chrono::system_clock::now();
	  std::chrono::duration<double> duration = current - start_op_time;
	  if (duration.count() * 1000000 < latency_cutoff)
	    latency_count++;
#else
	  query_success_count += map.find(HANDLE b[j]).has_value();
#endif
	} else if (op_types[k] == Insert) {
#ifdef UPSERT
	  if (upsert) {
	    if (map.upsert(HANDLE b[j], [] (std::optional<V> v) {return 123;})) {added++; update_success_count++;}
	  } else {
	    if (map.insert(HANDLE b[j], 123)) {added++; update_success_count++;}
	  } 
#else
	  if (map.insert(HANDLE b[j], 123)) {added++; update_success_count++;}
#endif
	} else { // (op_types[k] == Remove) 
	  if (map.remove(HANDLE b[j])) {removed++; update_success_count++;}
	}


	// wrap around if ran out of samples
	if (++j >= (i+1)*mp) j = i*mp;
	if (++k >= (i+1)*mp) k = i*mp + 1; // offset so different ops on different rounds
	cnt++;
	total++;
      }
    }, 1, true);
    auto current = std::chrono::system_clock::now();
    std::chrono::duration<double> duration = current - start;
    if (warmup && i==0) continue;
    
    size_t num_ops = parlay::reduce(totals);
    size_t queries = parlay::reduce(query_counts);
    double latency_count = (double) parlay::reduce(latency_counts);
    double mops = num_ops / (duration.count() * 1e6);
    bench_times.push_back(mops);
    std::cout << C.commandName() << ","
              << update_percent << "%update,"
              << "n=" << n << ","
              << "p=" << p << ","
              << "z=" << zipfian_param << ","
#ifdef Latency
      	      << latency_count / queries * 100.0 << "%@" << latency_cutoff << "usec,"
#endif
      	      << "grow=" << grow << ","
	      << "insert_mops=" << (int) imops << ","
              << "mops=" << (int) mops << std::endl;

    size_t updates = num_ops - queries;
    size_t queries_success = parlay::reduce(query_success_counts);
    size_t updates_success = parlay::reduce(update_success_counts);
    double qratio = (double) queries_success / queries;
    double uratio = (double) updates_success / updates;
    size_t final_cnt = map.size();
    long added = parlay::reduce(addeds);
    long removed = parlay::reduce(removeds);
    if (verbose)
      std::cout << "query success ratio = " << qratio
		<< ", update success ratio = " << uratio
		<< ", insertions = " << added
		<< ", removes = " << removed
		<< std::endl;
    if (qratio < .4 || qratio > .6)
      std::cout << "warning: query success ratio = " << qratio << std::endl;
    if (uratio < .4 || uratio > .6)
      std::cout << "warning: update success ratio = " << uratio << std::endl;
    if (initial_size + added - removed != final_cnt) {
      std::cout << "bad final size: intial size = " << initial_size
		<< ", net added " << (added - removed)
		<< ", final size = " << final_cnt 
		<< std::endl;
    }
  }
  #ifdef MEM_STATS
    if (verbose) {
      map_type::clear();
      map_type::stats();
    }
#endif
  }
  return std::tuple{ geometric_mean(insert_times),
      geometric_mean(bench_times)};
}
    
int main(int argc, char* argv[]) {
  commandLine P(argc,argv,"[-n <size>] [-r <rounds>] [-p <procs>] [-z <zipfian_param>] [-u <update percent>] [-verbose]");

  long n = P.getOptionIntValue("-n", 0);
  int p = P.getOptionIntValue("-p", parlay::num_workers());  
  int rounds = P.getOptionIntValue("-r", 2);
  double zipfian_param = P.getOptionDoubleValue("-z", -1.0);
  int update_percent = P.getOptionIntValue("-u", -1);
  bool upsert = P.getOption("-upsert");
  double trial_time = P.getOptionDoubleValue("-t", 1.0);
  double latency_cuttoff = P.getOptionDoubleValue("-latency", 10.0); // in miliseconds
  bool verbose = P.getOption("-verbose");
  bool warmup = !P.getOption("-nowarmup");
  bool grow = P.getOption("-grow");
  bool print_means = !P.getOption("-nomeans");

  std::vector<long> sizes {100000, 10000000};
  std::vector<int> percents{5, 50};
  std::vector<double> zipfians{0, .99};
  if (n != 0) sizes = std::vector<long>{n};
  if (update_percent != -1) percents = std::vector<int>{update_percent};
  if (zipfian_param != -1.0) zipfians = std::vector<double>{zipfian_param};

  parlay::sequence<std::tuple<double,double>> results;

  for (auto zipfian_param : zipfians) 
    for (auto update_percent : percents) {
      for (auto n : sizes) {
	results.push_back(test_loop(P, n, p, rounds, zipfian_param, update_percent, upsert,
				    trial_time, latency_cuttoff, verbose, warmup, grow));
      }
      if (print_means) std::cout << std::endl;
    }

  auto insert_times = parlay::map(results, [] (auto x) {return std::get<0>(x);});
  auto bench_times = parlay::map(results, [] (auto x) {return std::get<1>(x);});
  if (print_means) {
    std::cout << "benchmark geometric mean of mops = " << geometric_mean(bench_times) << std::endl;
    std::cout << "initial insert geometric mean of mops = " << geometric_mean(insert_times) << std::endl;
  }
  return false;
}
