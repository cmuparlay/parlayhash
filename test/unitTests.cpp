#include <iostream>
#include <string>
#include <unordered_set>
#include "parlay_hash/unordered_map.h"
#include "parlay_hash/unordered_set.h"

#include "gtest/gtest.h"

constexpr long num_threads = 100;
constexpr long test_size = 100000;

template <typename F>
void parallel_for(long n, F&& f) {
  auto g = [&] (long start, long end) {
             for (long i = start; i < std::min(end,n); i++) f(i);};
  long block_size = (n - 1) / num_threads + 1;
  std::vector<std::thread> threads(num_threads);
  for (int j = 0; j < num_threads; j++)
    threads[j] = std::thread(g, j * block_size, (j+1) * block_size);
  for (int i = 0; i < num_threads; i++)
    threads[i].join();
}

TEST(TestHash,TestSetEmpty) {
  parlay::parlay_unordered_set<std::string> set;
  ASSERT_EQ(set.size(), 0);
  ASSERT_TRUE(set.empty());
  set.Insert("hello");
  ASSERT_FALSE(set.empty());
}

TEST(TestHash,TestSetCount) {
  parlay::parlay_unordered_set<std::string> set;
  ASSERT_EQ(set.count("hello"), 0);
  set.Insert("hello");
  ASSERT_EQ(set.count("hello"), 1);
}

TEST(TestHash,TestSetInsertSize) {
  parlay::parlay_unordered_set<std::string> set;
  parallel_for(test_size, [&] (long i) {set.Insert(std::to_string(i));});
  ASSERT_EQ(set.size(), test_size);
}

TEST(TestHash,TestSetInsertElements) {
  parlay::parlay_unordered_set<std::string> set;
  parallel_for(test_size, [&] (long i) {set.Insert(std::to_string(i));});
  for (long i = 0; i < test_size; i++)
    ASSERT_TRUE(set.Find(std::to_string(i)));
  for (long i = test_size; i < 2*test_size; i++)
    ASSERT_FALSE(set.Find(std::to_string(i)));
}

TEST(TestHash,TestSetInsertRemoveSize) {
  ASSERT_TRUE(test_size % 2 == 0); // check that test size is even
  parlay::parlay_unordered_set<std::string> set;
  parallel_for(test_size, [&] (long i) {set.Insert(std::to_string(i));});
  parallel_for(test_size/2, [&] (long i) {set.Remove(std::to_string(2*i));});
  ASSERT_EQ(set.size(), test_size/2);
  parallel_for(test_size/2, [&] (long i) {set.Remove(std::to_string(2*i + 1));});
  ASSERT_EQ(set.size(), 0);
}

TEST(TestHash,TestSetInsertRemoveElements) {
  parlay::parlay_unordered_set<std::string> set;
  parallel_for(test_size, [&] (long i) {set.Insert(std::to_string(i));});
  parallel_for(test_size/2, [&] (long i) {set.Remove(std::to_string(2*i));});
  parallel_for(test_size/2, [&] (long i) {ASSERT_FALSE(set.Find(std::to_string(2*i)));});
  parallel_for(test_size/2, [&] (long i) {ASSERT_TRUE(set.Find(std::to_string(2*i+1)));});
}

TEST(TestHash,TestSetInitialSize) {
  for (int size = 0; size < 1024; size = 1 + 2 * size) {
    parlay::parlay_unordered_set<std::string> set(size);
    parallel_for(test_size, [&] (long i) {set.Insert(std::to_string(i));});
    ASSERT_EQ(set.size(), test_size);
  }
}

TEST(TestHash,TestSetIteratorSize) {
  parlay::parlay_unordered_set<std::string> set;
  parallel_for(test_size, [&] (long i) {set.Insert(std::to_string(i));});
  long cnt = 0;
  for (auto x : set) {cnt++;}
  ASSERT_EQ(cnt, test_size);
}

TEST(TestHash,TestSetIteratorMembers) {
  parlay::parlay_unordered_set<std::string> set;
  parallel_for(test_size, [&] (long i) {set.Insert(std::to_string(i));});
  std::unordered_set<std::string> std_set;
  for (auto x : set) { std_set.insert(x); }
  for (int i = 0; i < test_size; i++)
    ASSERT_TRUE(std_set.count(std::to_string(i)) == 1);
}

TEST(TestHash,TestSetInsertDelete) {
  parlay::parlay_unordered_set<std::string> set;
  std::atomic<long> inserted = 0;
  std::atomic<long> deleted = 0;
  parallel_for(test_size, [&] (long i) {
                            if (i % 2 == 0) inserted += set.Insert(std::to_string(i%79));
                            else deleted += set.Remove(std::to_string(i%79)); });
  ASSERT_TRUE(inserted - deleted == set.size());
}

TEST(TestHash,TestSetClear) {
  parlay::parlay_unordered_set<std::string> set;
  parallel_for(test_size, [&] (long i) {set.Insert(std::to_string(i));});
  set.clear();
  ASSERT_EQ(set.size(), 0);
  ASSERT_TRUE(set.empty());
}

TEST(TestHash,TestMapEmpty) {
  parlay::parlay_unordered_map<std::string,std::string> map;
  ASSERT_EQ(map.size(), 0);
  ASSERT_TRUE(map.empty());
  map.Insert("hello","1");
  ASSERT_FALSE(map.empty());
}

TEST(TestHash,TestMapCount) {
    parlay::parlay_unordered_map<std::string,std::string> map;
  ASSERT_EQ(map.count("hello"), 0);
  map.Insert("hello", "1");
  ASSERT_EQ(map.count("hello"), 1);
}

TEST(TestHash,TestMapInsertSize) {
  parlay::parlay_unordered_map<std::string,std::string> map;
  parallel_for(test_size, [&] (long i) {map.Insert(std::to_string(i), std::to_string(i));});
  ASSERT_EQ(map.size(), test_size);
}

TEST(TestHash,TestMapInsertElements) {
  parlay::parlay_unordered_map<std::string,std::string> map;
  parallel_for(test_size, [&] (long i) {map.Insert(std::to_string(i), std::to_string(i));});
  for (long i = 0; i < test_size; i++)
    ASSERT_TRUE(*map.Find(std::to_string(i)) == std::to_string(i));
  for (long i = test_size; i < 2*test_size; i++)
    ASSERT_FALSE(map.Find(std::to_string(i)).has_value());
}

TEST(TestHash,TestMapInsertRemoveSize) {
  ASSERT_TRUE(test_size % 2 == 0); // check that test size is even
  parlay::parlay_unordered_map<std::string,std::string> map;
  parallel_for(test_size, [&] (long i) {map.Insert(std::to_string(i), std::to_string(i));});
  parallel_for(test_size/2, [&] (long i) {map.Remove(std::to_string(2*i));});
  ASSERT_EQ(map.size(), test_size/2);
  parallel_for(test_size/2, [&] (long i) {map.Remove(std::to_string(2*i + 1));});
  ASSERT_EQ(map.size(), 0);
}

TEST(TestHash,TestMapInsertRemoveElements) {
  parlay::parlay_unordered_map<std::string,std::string> map;
  parallel_for(test_size, [&] (long i) {map.Insert(std::to_string(i), std::to_string(i));});
  parallel_for(test_size/2, [&] (long i) {map.Remove(std::to_string(2*i));});
  parallel_for(test_size/2, [&] (long i) {ASSERT_FALSE(map.Find(std::to_string(2*i)).has_value());});
  parallel_for(test_size/2, [&] (long i) {ASSERT_EQ(*map.Find(std::to_string(2*i+1)), std::to_string(2*i+1));});
}

TEST(TestHash,TestMapInitialSize) {
  for (int size = 0; size < 1024; size = 1 + 2 * size) {
    parlay::parlay_unordered_map<std::string,std::string> map(size);
    parallel_for(test_size, [&] (long i) {map.Insert(std::to_string(i),std::to_string(i));});
    ASSERT_EQ(map.size(), test_size);
  }
}

TEST(TestHash,TestMapIteratorSize) {
  parlay::parlay_unordered_map<std::string,std::string> map;
  parallel_for(test_size, [&] (long i) {map.Insert(std::to_string(i), std::to_string(i));});
  long cnt = 0;
  for (auto x : map) {cnt++;}
  ASSERT_EQ(cnt, test_size);
}

TEST(TestHash,TestMapIteratorMembers) {
  parlay::parlay_unordered_map<std::string,std::string> map;
  parallel_for(test_size, [&] (long i) {map.Insert(std::to_string(i), std::to_string(i));});
  std::unordered_map<std::string,std::string> std_map;
  for (auto x : map) { std_map.insert(x); }
  for (int i = 0; i < test_size; i++)
    ASSERT_TRUE(std_map.count(std::to_string(i)) == 1);
}

TEST(TestHash,TestMapInsertDelete) {
  parlay::parlay_unordered_map<std::string,std::string> map;
  std::atomic<long> inserted = 0;
  std::atomic<long> deleted = 0;
  parallel_for(test_size, [&] (long i) {
                            if (i % 2 == 0) inserted += !map.Insert(std::to_string(i%79),"0").has_value();
                            else deleted += map.Remove(std::to_string(i%79)).has_value(); });
  ASSERT_TRUE(inserted - deleted == map.size());
}

TEST(TestHash,TestMapClear) {
  parlay::parlay_unordered_map<std::string,std::string> map;
  parallel_for(test_size, [&] (long i) {map.Insert(std::to_string(i), std::to_string(i));});
  map.clear();
  ASSERT_EQ(map.size(), 0);
  ASSERT_TRUE(map.empty());
}
