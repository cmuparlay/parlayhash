set(SOURCES test_map.cpp)

function(add_benchmark NAME DIRECTORY LINKS OPTIONS DEFS)
  add_executable(${NAME} ${SOURCES})
  target_link_libraries(${NAME} PRIVATE parlay ${LINKS})
  target_compile_options(${NAME} PRIVATE ${OPTIONS})
  target_compile_definitions(${NAME} PRIVATE ${DEFS})
  target_include_directories(${NAME} PRIVATE ${PARLAYHASH_SOURCE_DIR}/${DIRECTORY}/${NAME})
endfunction()

add_benchmark(hash_nogrow include "" "" "UPSERT")
add_benchmark(hash_grow include "" "" "UPSERT")
add_benchmark(hash_opt include "" "" "")
add_benchmark(hash_list include "" "" "UPSERT")
add_benchmark(std_hash other "" "" "")
add_benchmark(std_sharded other "" "" "")
add_benchmark(libcuckoo other "" "" "")
add_benchmark(growt other "" "-mcx16" "")
add_benchmark(parallel_hashmap other "" "" "")

find_package(GTest)
find_package(absl)
#add_subdirectory(abseil-cpp)
if (absl_FOUND)
  add_benchmark(abseil other absl::flat_hash_map "" "")
  add_benchmark(abseil_sharded other absl::flat_hash_map "" "")
endif()

find_package(folly)
if (folly_FOUND)
  add_benchmark(folly_hash other "folly;glog;dl;pthread;double-conversion;fmt;gflags;unwind" "" "")
  add_benchmark(folly_sharded other "folly;glog;dl;pthread;double-conversion;fmt;gflags;unwind" "" "")
endif()

find_package(TBB)
IF (TBB_FOUND)
  add_benchmark(tbb_hash other TBB::tbb "" "")
endif()

# set(BOOST_DIR ${PARLAYHASH_SOURCE_DIR}/build/benchmarks/boost_1_83_0)

# We have to manually specify Boost's location since we are using the latest
# cutting-edge Boost version, and FindBoost.cmake can not find Boost.Unordered
if (BOOST_DIR)
  add_benchmark(boost_hash other "" "" "")
  target_include_directories(boost_hash PRIVATE ${BOOST_DIR})
endif()

set(BENCH_FILES "runtests.py" "run_graphs")

function(copy_bench_file NAME)
  file(COPY ${CMAKE_CURRENT_SOURCE_DIR}/${NAME}
    DESTINATION ${CMAKE_CURRENT_BINARY_DIR})
endfunction()

foreach(file ${BENCH_FILES})
  copy_bench_file(${file})
endforeach()

