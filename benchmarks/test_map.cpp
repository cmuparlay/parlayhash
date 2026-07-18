#include <array>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <iostream>
#include <sstream>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

#ifndef GOOGLE
#include "parse_command_line.h"
#include "trigrams.h"
#include "zipfian.h"
#include "parlay/parallel.h"
#include "parlay/primitives.h"
#include "parlay/random.h"
#include "parlay/sequence.h"
#include "parlay/utilities.h"
#include "parlay/io.h"  
#else
#include "base/init_google.h"
#include "file/base/path.h"
#include "third_party/flock/benchmarks/trigrams.h"
#include "third_party/flock/benchmarks/zipfian.h"
#include "third_party/graph_mining/in_memory/parallel/scheduler.h"
#include "third_party/parlay/include/parlay/parallel.h"
#include "third_party/parlay/include/parlay/primitives.h"
#include "third_party/parlay/include/parlay/random.h"
#include "third_party/parlay/include/parlay/sequence.h"
#include "third_party/parlay/include/parlay/utilities.h"
#include "third_party/parlay/include/parlay/io.h"
#endif

#define PARLAY_USE_STD_ALLOC 1

#ifdef JEMALLOC
#include <jemalloc/jemalloc.h>
#endif
#ifdef TCMALLOC
#ifdef GOOGLE
#include "third_party/tcmalloc/malloc_extension.h"
#else
#include "tcmalloc/malloc_extension.h"
#endif
#endif

//#define USE_ABSL_FLAGS

#ifdef USE_ABSL_FLAGS
#include "third_party/absl/flags/flag.h"
// #include "third_party/absl/flags/parse.h"
ABSL_FLAG(int, n, 0, "Table Size (0 will use multiple sizes)");
ABSL_FLAG(int, r, 2, "Number of rounds");
ABSL_FLAG(int, p, 0, "Number of threads (0 will use hardware concurrency)");
ABSL_FLAG(int, u, -1,
          "Percent of operations that are updates (-1 will use multiple)");
ABSL_FLAG(double, z, -1.0, "Zipfian parameter (-1 will use multiple)");
// ABSL_FLAG(bool, upsert, false, "Use upsert instead of insert");
ABSL_FLAG(double, t, 1.0, "Time to run for each trial");
ABSL_FLAG(double, latency, 0.0,
          "Measure percent of operations with more than given latency");
ABSL_FLAG(bool, verbose, false, "Show detailed information");
ABSL_FLAG(bool, nowarmup, false, "Do not Run one warmup round");
ABSL_FLAG(bool, grow, false, "Start with table of size 1");
ABSL_FLAG(bool, nomeans, false, "Don't print means");
ABSL_FLAG(double, expand, 1.0, "Start with table of size expand * n");
ABSL_FLAG(bool, string, false, "Only strings");
ABSL_FLAG(bool, nostr, false, "No Strings");
ABSL_FLAG(bool, full, false, "Run full set of benchmarks");
ABSL_FLAG(bool, norepeat, false, "Do not repeat the keys");
#else
#include "parse_command_line.h"  // "parse_command_line.h"
#endif

using str_type = parlay::chars;
auto to_string(const std::string& s) {return parlay::to_chars(s);}
//using str_type = std::string;
//auto to_string(const std::string& s) { return s; }

using K = uint64_t;
using V = uint64_t;

#include "unordered_map.h"

// growt requires handles, rest do not
#ifdef USE_HANDLE
#define HANDLE handle,
#else
#define HANDLE
#endif

struct IntHash {
  using is_avalanching = void;  // used to avoid secondary hashing
  std::size_t operator()(K const& k) const noexcept {
    auto x = k * UINT64_C(0xbf58476d1ce4e5b9);  // linear transform
    return (x ^ (x >> 31));                     // non-linear transform
  }
};

struct StringHash {
  using is_avalanching = void;  // used to avoid secondary hashing
  std::size_t operator()(str_type const& k) const noexcept {
    return parlay::hash<str_type>{}(k);
  }
};

double geometric_mean(const parlay::sequence<double>& vals) {
  double product = 1;
  for (auto x : vals) product = product * x;
  return pow(product, 1.0 / vals.size());
}

// zipfian parameter [0:1) (0 is uniform, .99 is high skew)
template <typename int_type>
std::pair<parlay::sequence<int_type>, parlay::sequence<int_type>>
generate_integer_distribution(int64_t n,  // num entries in map
                              int64_t p, double zipfian_param) {
  // total samples used
  int64_t m = 10 * n + 1000 * p;

  // generate 2*n unique numbers in random order
  auto x = parlay::delayed_tabulate(1.2 * 2 * n, [&](size_t i) {
    return (int_type)(parlay::hash64(i));
  });
  auto y = parlay::random_shuffle(parlay::remove_duplicates(x));
  auto a = parlay::tabulate(2 * n, [&](int64_t i) { return y[i]; });

  // take m numbers from a in uniform or zipfian distribution
  parlay::sequence<int_type> b;
  if (zipfian_param != 0.0) {
    auto z = zipfian(2 * n, zipfian_param);
    b = parlay::tabulate(m, [&](int i) { return a[z(i)]; });
    a = parlay::random_shuffle(a);
  } else {
    b = parlay::tabulate(m,
                         [&](int i) { return a[parlay::hash64(i) % (2 * n)]; });
  }
  return std::pair(a, b);
}

template <typename int_type>
parlay::sequence<int_type> generate_integer_distribution_no_repeat(
    int64_t n,  // num entries in map
    int64_t p, double zipfian_param) {
  int m = 100 * (n + p);
  // take m numbers from a in uniform or zipfian distribution
  if (zipfian_param != 0.0) {
    auto z = zipfian(m, zipfian_param);
    return parlay::tabulate(m, [&](int i) { return (int_type)z(i); });
  } else {
    return parlay::tabulate(
			    m, [&](int64_t i) { return (int_type) (parlay::hash64(i)); });
  }
}

std::pair<parlay::sequence<str_type>, parlay::sequence<str_type>>
generate_string_distribution(int64_t n) {
  auto ts = trigramWords<str_type>(n);
  auto b = parlay::map(ts, [](const auto& s) { return to_string(s); });
  auto a = parlay::random_shuffle(parlay::remove_duplicates(b));
  return std::pair(a, b);
}

#ifdef JEMALLOC
size_t get_allocated_bytes() {
  size_t epoch = 1;
  size_t sz, allocated;
  sz = sizeof(size_t);
  mallctl("thread.tcache.flush", NULL, NULL, NULL, 0);
  mallctl("epoch", NULL, NULL, &epoch, sizeof(epoch));
  mallctl("stats.allocated", &allocated, &sz, NULL, 0);
  return allocated;
}
#elif defined(TCMALLOC)
size_t get_allocated_bytes() {
  auto allocated = tcmalloc::MallocExtension::GetNumericProperty(
      "generic.current_allocated_bytes");
  return allocated.value_or(0);
}
#else
size_t get_allocated_bytes() { return 1; }
#endif

template <typename Map>
std::tuple<double, double, double, double, double> test_loop(
    const std::string& command_name, std::string info,
    const parlay::sequence<typename Map::K>& a,
    const parlay::sequence<typename Map::K>& b,
    int64_t p,       // num threads
    int64_t rounds,  // num trials
    // percent of operations that are either insert or delete (1/2 each)
    int update_percent,
    bool upsert,            // use upsert instead of insert
    double trial_time,      // time to run one trial
    double latency_cutoff,  // cutoff to measure percent below
    bool verbose,           // show some more info
    bool warmup,            // run one warmup round
    bool grow,              // start with table of size 1
    double expand,          // start with table of size expand x n
    bool no_repeat          // do not reuse keys
) {
  enum op_type : char { Find, Insert, Remove };
  int64_t n = a.size() / 2;
  int64_t m = b.size();

  // generate the operation types with update_percent updates
  // half the updates will be inserts and half removes
  auto op_types = parlay::tabulate(m, [&](size_t i) -> op_type {
    auto h = parlay::hash64(m + i) % 200;
    if (h < update_percent) {
      return Insert;
    } else {
      if (h < 2 * update_percent)
        return Remove;
      else
        return Find;
    }
  });

  parlay::sequence<double> insert_times;
  parlay::sequence<double> bench_times;
  parlay::sequence<double> bytes_pes;
  parlay::sequence<double> query_latency_percents;
  parlay::sequence<double> update_latency_percents;

  size_t mp = m / p;
  size_t np = n / p;

  if (no_repeat) {
    // if no_repeat then figure out actual number of keys inserted at
    // the start
    auto a = parlay::flatten(parlay::tabulate(p, [&](int64_t i) {
      return parlay::tabulate(np, [&](int64_t j) { return b[i * mp + j]; });
    }));
    n = parlay::remove_duplicates(a).size();
  }

  for (int i = 0; i < rounds + warmup; i++) {
    {
      int64_t mem_at_start = get_allocated_bytes();
      Map map = grow ? Map(1) : Map(static_cast<int64_t>(n * expand));

      auto start_insert = std::chrono::system_clock::now();

      // initialize the map with n distinct elements
      if (no_repeat)
        parlay::parallel_for(
            0, p,
            [&](int64_t i) {
              for (int64_t j = i * mp; j < (i * mp) + np; j++) map.insert(b[j]);
            },
            1, true);
      else {
        if (p == 1) {
          for (size_t i = 0; i < n; ++i) map.insert(a[i]);
        } else {
          parlay::parallel_for(0, n, [&](size_t i) { map.insert(a[i]); });
        }
      }

      std::chrono::duration<double> insert_time =
          std::chrono::system_clock::now() - start_insert;
      int64_t mem_after_insert = get_allocated_bytes();

      if (map.size() != n)
        std::cout << "bad initial size = " << map.size() << std::endl;

      double imops = n / insert_time.count() / 1e6;
      if (!warmup || i > 0) insert_times.push_back(imops);

      int64_t initial_size = map.size();

      // keep track of some statistics, one entry per thread
      parlay::sequence<int64_t> totals(p);
      parlay::sequence<int64_t> addeds(p);
      parlay::sequence<int64_t> removeds(p);
      parlay::sequence<int64_t> query_counts(p);
      parlay::sequence<int64_t> query_success_counts(p);
      parlay::sequence<int64_t> update_success_counts(p);
      parlay::sequence<int64_t> query_latency_counts(p);
      parlay::sequence<int64_t> update_latency_counts(p);

      if (verbose) std::cout << "entries inserted" << std::endl;

      auto start = std::chrono::system_clock::now();

      auto run_op = [&](auto op, int64_t& counter) {
        if (latency_cutoff > 0) {
          auto start_op_time = std::chrono::system_clock::now();
          op();
          auto current = std::chrono::system_clock::now();
          std::chrono::duration<double> duration = current - start_op_time;
          if (duration.count() * 1000000 < latency_cutoff) counter++;
        } else {
          op();
        }
      };

      // start up p threads, each doing a sequence of operations
      parlay::parallel_for(
          0, p,
          [&](size_t i) {
            int cnt = 0;
            size_t j = i * mp;
            size_t k = no_repeat ? i * mp + np : i * mp;
            size_t total = 0;
            int64_t added = 0;
            int64_t removed = 0;
            int64_t query_count = 0;
            int64_t query_success_count = 0;
            int64_t update_success_count = 0;
            int64_t query_latency_count = 0.0;
            int64_t update_latency_count = 0.0;
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
                  query_latency_counts[i] = query_latency_count;
                  update_latency_counts[i] = update_latency_count;
                  return;
                }
              }

              if (no_repeat) {
                if (op_types[j] == Insert) {
                  total++;
                  run_op(
                      [&] {
                        if (map.remove(b[j])) {
                          removed++;
                          update_success_count++;
                        }
                      },
                      update_latency_count);
                }
                if (op_types[k] == Find) {
                  query_count++;
                  total++;
                  run_op([&] { query_success_count += map.find(b[k]); },
                         query_latency_count);
                } else if (op_types[k] == Insert) {
                  total++;
                  run_op(
                      [&] {
                        if (map.insert(b[k])) {
                          added++;
                          update_success_count++;
                        }
                      },
                      update_latency_count);
                }

                // wrap around if overflow
                if (j++ == (i + 1) * mp) j = i * mp;
                if (k++ == (i + 1) * mp) k = i * mp;
                cnt++;
              } else {
                // do one of find, insert, or remove
                if (op_types[k] == Find) {
                  query_count++;
                  run_op([&] { query_success_count += map.find(b[j]); },
                         query_latency_count);
                } else if (op_types[k] == Insert) {
                  run_op(
                      [&] {
                        if (map.insert(b[j])) {
                          added++;
                          update_success_count++;
                        }
                      },
                      update_latency_count);
                } else {  // (op_types[k] == Remove)
                  run_op(
                      [&] {
                        if (map.remove(b[j])) {
                          removed++;
                          update_success_count++;
                        }
                      },
                      update_latency_count);
                }

                // wrap around if ran out of samples
                if (++j >= (i + 1) * mp) j = i * mp;
                // offset so different ops on different rounds
                if (++k >= (i + 1) * mp) k = i * mp + 1;
                cnt++;
                total++;
              }
            }
          },
          1, true);
      auto current = std::chrono::system_clock::now();
      int64_t final_size = map.size();

      // int64_t mem_at_end = jemalloc_get_allocated();

      std::chrono::duration<double> duration = current - start;
      if (warmup && i == 0) continue;

      size_t num_ops = parlay::reduce(totals);
      size_t queries = parlay::reduce(query_counts);
      size_t updates = num_ops - queries;

      double query_latency_count = (double)parlay::reduce(query_latency_counts);
      double query_latency_percent =
          (queries == 0) ? 100.0 : query_latency_count / queries * 100.0;
      if (queries > 0) query_latency_percents.push_back(query_latency_percent);
      double update_latency_count =
          (double)parlay::reduce(update_latency_counts);
      double update_latency_percent =
          (updates == 0) ? 100.0 : update_latency_count / updates * 100.0;
      if (updates > 0)
        update_latency_percents.push_back(update_latency_percent);

      double mops = num_ops / (duration.count() * 1e6);
      bench_times.push_back(mops);

      double bytes_pe =
          ((double)(mem_after_insert - mem_at_start)) / final_size;
      bytes_pes.push_back(bytes_pe);

      std::cout << command_name << ","
                << "update=" << update_percent << "%,"
                << "n=" << n << ","
                << "p=" << p << "," << info << ","
                << "grow=" << grow << ","
                << "mem_pe=" << (int)bytes_pe << ","
                << "insert_mops=" << (int)imops << ",";
      if (latency_cutoff > 0) {
        std::cout << "query_latency=" << query_latency_percent << "%@"
                  << latency_cutoff << "usec,"
                  << "update_latency=" << update_latency_percent << "%@"
                  << latency_cutoff << "usec" << std::endl;
      } else {
        std::cout << "mops=" << (int)mops << std::endl;
      }

      size_t queries_success = parlay::reduce(query_success_counts);
      size_t updates_success = parlay::reduce(update_success_counts);
      double qratio = (double)queries_success / queries;
      double uratio = (double)updates_success / updates;
      size_t final_cnt = map.size();
      int64_t added = parlay::reduce(addeds);
      int64_t removed = parlay::reduce(removeds);
      if (verbose)
        std::cout << "query success ratio = " << qratio
                  << ", update success ratio = " << uratio
                  << ", insertions = " << added << ", removes = " << removed
                  << std::endl;
      if (!no_repeat && (qratio < .4 || qratio > .6))
        std::cout << "warning: query success ratio = " << qratio << std::endl;
      if (!no_repeat && (uratio < .4 || uratio > .6))
        std::cout << "warning: update success ratio = " << uratio << std::endl;
      if (initial_size + added - removed != final_cnt) {
        std::cout << "bad final size: initial size = " << initial_size
                  << ", net added " << (added - removed)
                  << ", final size = " << final_cnt << std::endl;
      }
    }
#ifdef MEM_STATS
    if (verbose) {
      map_type::clear();
      map_type::stats();
    }
#endif
  }
  return std::tuple{geometric_mean(insert_times), geometric_mean(bench_times),
                    geometric_mean(bytes_pes),
                    geometric_mean(query_latency_percents),
                    geometric_mean(update_latency_percents)};
}

template <typename K_, typename V_, typename Hash, int val_len>
struct bench_map {
  using K = K_;
  using V = std::array<V_, val_len>;
  V default_val;
  unordered_map<K, V, Hash> m;
  explicit bench_map(size_t n) : m(n) { default_val[0] = 1; }
  int find(const K& k) {
    auto r = m.find(k);
    return r.has_value() ? (*r)[0] : 0;
  }
  bool insert(const K& k) { return m.insert(k, default_val); }
  bool remove(const K& k) { return m.remove(k); }
  int64_t size() { return m.size(); }
};

#ifdef USE_SET
template <typename K_, typename Hash>
struct bench_set {
  using K = K_;
  unordered_set<K, Hash> m;
  explicit bench_set(size_t n) : m(n) {}
  int find(const K& k) { return (m.find(k)) ? 1 : 0; }
  bool insert(const K& k) { return m.insert(k); }
  bool remove(const K& k) { return m.remove(k); }
  int64_t size() { return m.size(); }
};
#else
template <typename K_, typename Hash>
struct bench_set {
  using K = K_;
  unordered_map<K, bool, Hash> m;
  explicit bench_set(size_t n) : m(n) {}
  int find(const K& k) { return (m.find(k).has_value()) ? 1 : 0; }
  bool insert(const K& k) { return m.insert(k, true); }
  bool remove(const K& k) { return m.remove(k); }
  int64_t size() { return m.size(); }
};
#endif

int main(int argc, char* argv[]) {
#ifdef GOOGLE
  InitGoogle(argv[0], &argc, &argv, /*remove_flags=*/false);
  graph_mining::in_memory::ParallelSchedulerReference scheduler;
#endif
  
#ifdef USE_ABSL_FLAGS
  // absl::ParseCommandLine(argc, argv);
  int n = absl::GetFlag(FLAGS_n);
  int p = absl::GetFlag(FLAGS_p) > 0 ? absl::GetFlag(FLAGS_p)
                                     : parlay::num_workers();
  int rounds = absl::GetFlag(FLAGS_r);
  double zipfian_param = absl::GetFlag(FLAGS_z);
  int update_percent = absl::GetFlag(FLAGS_u);
  bool upsert = false;  // absl::GetFlag(FLAGS_upsert);
  double trial_time = absl::GetFlag(FLAGS_t);
  double latency_cutoff = absl::GetFlag(FLAGS_latency);
  bool verbose = absl::GetFlag(FLAGS_verbose);
  bool warmup = !absl::GetFlag(FLAGS_nowarmup);
  bool grow = absl::GetFlag(FLAGS_grow);
  bool print_means = !absl::GetFlag(FLAGS_nomeans);
  double expand = absl::GetFlag(FLAGS_expand);
  bool string_only = absl::GetFlag(FLAGS_string);
  bool no_string = absl::GetFlag(FLAGS_nostr);
  bool full = absl::GetFlag(FLAGS_full);
  bool no_repeat = absl::GetFlag(FLAGS_norepeat);
#else
  commandLine P(argc, argv,
                "[-n <size>] [-r <rounds>] [-p <procs>] [-z <zipfian_param>] "
                "[-u <update percent>] [-verbose]");
  int64_t n = P.getOptionIntValue("-n", 0);
  int p = P.getOptionIntValue("-p", parlay::num_workers());
  int rounds = P.getOptionIntValue("-r", 2);
  double zipfian_param = P.getOptionDoubleValue("-z", -1.0);
  int update_percent = P.getOptionIntValue("-u", -1);
  bool upsert = P.getOption("-upsert");
  double trial_time = P.getOptionDoubleValue("-t", 1.0);
  // latency in milliseconds
  double latency_cutoff = P.getOptionDoubleValue("-latency", 0.0);
  bool verbose = P.getOption("-verbose");
  bool warmup = !P.getOption("-nowarmup");
  bool grow = P.getOption("-grow");
  bool print_means = !P.getOption("-nomeans");
  double expand = P.getOptionIntValue("-expand", 1);
  bool string_only = P.getOption("-string");
  bool no_string = P.getOption("-nostring");
  bool full = P.getOption("-full");
  bool no_repeat = P.getOption("-norepeat");
#endif

#if GOOGLE
  std::string command_name(file::Basename(argv[0]));
#else
  std::string command_name(argv[0]);
#endif
  
  std::vector<int64_t> sizes;
  std::vector<int> percents;
  std::vector<double> zipfians;
  if (full) {
    sizes = std::vector<int64_t>({10000, 1000000, 100000000});
    percents = std::vector<int>({0, 1, 10, 50});
    zipfians = std::vector<double>({0, .99});
  } else {
    sizes = std::vector<int64_t>({10000, 10000000});
    percents = std::vector<int>({5, 50});
    zipfians = std::vector<double>({0, .99});
  }
  if (n != 0) sizes = std::vector<int64_t>{n};
  if (update_percent != -1) percents = std::vector<int>{update_percent};
  if (zipfian_param != -1.0) zipfians = std::vector<double>{zipfian_param};

  parlay::sequence<double> insert_times;
  parlay::sequence<double> bench_times;
  parlay::sequence<double> byte_sizes;
  parlay::sequence<double> q_latencies;
  parlay::sequence<double> u_latencies;

  using int_type = uint64_t;
  using int_map_type = bench_map<int_type, int_type, IntHash, 1>;

  if (!string_only) {
    double byte_size, insert_time;
    for (auto zipfian_param : zipfians) {
      for (auto n : sizes) {
        parlay::sequence<int_type> a;
        parlay::sequence<int_type> b;
        std::stringstream str;
        if (no_repeat) {
          b = generate_integer_distribution_no_repeat<int_type>(n, p, zipfian_param);
          // only used for its length
          a = parlay::tabulate(2 * n, [&](int64_t i) { return (int_type) 0; });
          str << "long_long_nr,z=" << zipfian_param;
        } else {
          std::tie(a,b) = generate_integer_distribution<int_type>(n, p, zipfian_param);
          str << "long_long,z=" << zipfian_param;
        }

        for (auto update_percent : percents) {
          std::tuple<double, double, double, double, double> r;
          r = test_loop<int_map_type>(command_name, str.str(), a, b, p,
                                      rounds, update_percent, upsert,
                                      trial_time, latency_cutoff, verbose,
                                      warmup, grow, expand, no_repeat);
          auto [itime, btime, size, q_latency, u_latency] = r;
          bench_times.push_back(btime);
          if (update_percent < 100) q_latencies.push_back(q_latency);
          if (update_percent > 0) u_latencies.push_back(u_latency);
          insert_time = itime;
          byte_size = size;
        }
        if (print_means) std::cout << std::endl;
      }
    }
    byte_sizes.push_back(byte_size);
    insert_times.push_back(insert_time);

    using small_int_type = int;
    using int_set_type = bench_set<small_int_type, IntHash>;

    {
      double zipfian_param = zipfians[0];
      int64_t local_update_percent = 10;
      if (update_percent != -1) local_update_percent = update_percent;
      for (auto n : sizes) {
        parlay::sequence<small_int_type> a;
        parlay::sequence<small_int_type> b;
        std::stringstream str;
        if (no_repeat) {
          b = generate_integer_distribution_no_repeat<small_int_type>(n, p, zipfian_param);
          // only used for its length
          a = parlay::tabulate(2 * n, [&](int64_t i) { return (small_int_type) 0; });
          str << "int_nr,z=" << zipfian_param;
        } else {
          std::tie(a,b) = generate_integer_distribution<small_int_type>(n, p, zipfian_param);
          str << "int,z=" << zipfian_param;
        }
        auto [itime, btime, size, q_latency, u_latency] =
            test_loop<int_set_type>(command_name, str.str(), a, b, p, rounds,
                                    local_update_percent, upsert, trial_time,
                                    latency_cutoff, verbose, warmup, grow,
                                    expand, no_repeat);
        bench_times.push_back(btime);
        if (local_update_percent < 100) q_latencies.push_back(q_latency);
        if (local_update_percent > 0) u_latencies.push_back(u_latency);
        insert_time = itime;
        byte_size = size;
      }
    }
    if (print_means) std::cout << std::endl;
    byte_sizes.push_back(byte_size);
    insert_times.push_back(insert_time);
  }

  using string_map_type = bench_map<str_type, int64_t, StringHash, 2>;
  if (!no_string) {
    int cnt = 0;
    for (auto update_percent : percents) {
      int64_t n = 20000000;
      auto [a, b] = generate_string_distribution(n);
      std::stringstream str;
      str << "string_2xlong,trigram";
      auto [itime, btime, size, q_latency, u_latency] =
          test_loop<string_map_type>(
              command_name, str.str(), a, b, p, rounds, update_percent, upsert,
              trial_time, latency_cutoff, verbose, warmup, grow, expand, false);
      if (cnt++ == 0) {
        byte_sizes.push_back(size);
        insert_times.push_back(itime);
      }
      bench_times.push_back(btime);
      if (update_percent < 100) q_latencies.push_back(q_latency);
      if (update_percent > 0) u_latencies.push_back(u_latency);
    }
  }
  if (print_means) std::cout << std::endl;

  if (print_means) {
    if (latency_cutoff > 0) {
      std::cout << command_name << ": "
                << "query latency = " << geometric_mean(q_latencies) << "%@"
                << latency_cutoff << "usecs" << std::endl;
      std::cout << command_name << ": "
                << "update latency = " << geometric_mean(u_latencies) << "%@"
                << latency_cutoff << "usecs" << std::endl;
    } else {
      std::cout << command_name << ": "
                << "initial insert geometric mean of mops = "
                << geometric_mean(insert_times) << std::endl;
      std::cout << command_name << ": "
                << "benchmark geometric mean of mops = "
                << geometric_mean(bench_times) << std::endl;
#if defined(JEMALLOC) || defined(TCMALLOC)
      std::cout << command_name << ": "
                << "bytes/element geometric mean = "
                << geometric_mean(byte_sizes) << std::endl;
#endif
    }
  }
  return 0;
}
