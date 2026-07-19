set(SOURCES test_map.cpp)
find_library(JEMALLOC_LIB jemalloc)
if(NOT JEMALLOC_LIB)
  message(FATAL_ERROR "Could not find jemalloc.")
else()
  message("-- Found jemalloc: ${JEMALLOC_LIB}")
  set(COMMON_DEFS JEMALLOC)
  set(COMMON_LINKS ${JEMALLOC_LIB})
endif()

function(add_benchmark NAME_ DIRECTORY LINKS OPTIONS DEFS)
  set(NAME ${NAME_}${DEFS})
  add_executable(${NAME} ${SOURCES})
  target_link_libraries(${NAME} PRIVATE parlay ${LINKS} ${COMMON_LINKS})
  target_compile_options(${NAME} PRIVATE ${OPTIONS})
  target_compile_definitions(${NAME} PRIVATE ${DEFS})
  target_compile_definitions(${NAME} PRIVATE ${COMMON_DEFS})
  target_include_directories(${NAME} PRIVATE ${PARLAYHASH_SOURCE_DIR}/${DIRECTORY}/${NAME_})
endfunction()

find_package(GTest)
find_package(absl)

add_benchmark(old_parlay_hash other "" "" "")
add_benchmark(parlay_hash other "absl::flags;absl::flags_parse" "" "")
add_benchmark(parlay_hash other "absl::flags;absl::flags_parse" "" "lf")
add_benchmark(parlay_hash other "absl::flags;absl::flags_parse" "" "wf")
add_benchmark(parlay_hash other "absl::flags;absl::flags_parse" "" "noopt")
add_benchmark(parlay_hash other "absl::flags;absl::flags_parse" "" "indirect")
add_benchmark(std_hash other "" "" "")
add_benchmark(std_sharded other "" "" "")
add_benchmark(libcuckoo other "" "" "")
add_benchmark(parallel_hashmap other "" "" "")
add_benchmark(seq_hash other "" "" "")

find_package(absl CONFIG)
if(NOT absl_FOUND)
  message(STATUS "Abseil not found, fetching from GitHub...")
  include(FetchContent)
  FetchContent_Declare(
    abseil-cpp
    GIT_REPOSITORY https://github.com/abseil/abseil-cpp.git
    # Using a recent LTS release
    GIT_TAG        20240116.2
  )
  set(ABSL_PROPAGATE_CXX_STD ON CACHE BOOL "" FORCE)
  # We only need a subset, but FetchContent_MakeAvailable will configure all.
  # We can select what we need when linking.
  FetchContent_MakeAvailable(abseil-cpp)
endif()

#add_subdirectory(abseil-cpp)
#if (absl_FOUND)
add_benchmark(abseil other absl::flat_hash_map "" "")
add_benchmark(abseil_sharded other absl::flat_hash_map "" "")
#endif()

find_package(Highway CONFIG)
if(NOT Highway_FOUND)
  message(STATUS "Highway not found, fetching from GitHub...")
  include(FetchContent)
  
  # Disable Highway's own tests and examples to avoid target clashes (e.g. gtest)
  set(HWY_ENABLE_TESTS OFF CACHE BOOL "Disable Highway tests" FORCE)
  set(HWY_ENABLE_EXAMPLES OFF CACHE BOOL "Disable Highway examples" FORCE)
  
  FetchContent_Declare(
    highway
    GIT_REPOSITORY https://github.com/google/highway.git
    GIT_TAG        1.2.0 # Or appropriate version
  )
  FetchContent_MakeAvailable(highway)
endif()

add_benchmark(swiss_parlay other "absl::synchronization;absl::base;hwy" "" "")

find_package(folly)
if (folly_FOUND)
  add_benchmark(folly_hash other "folly;glog;dl;pthread;double-conversion;fmt;gflags;unwind" "" "")
  add_benchmark(folly_sharded other "folly;glog;dl;pthread;double-conversion;fmt;gflags;unwind" "" "")
  add_benchmark(folly_F14 other "folly;glog;dl;pthread;double-conversion;fmt;gflags;unwind" "" "")
endif()

find_package(TBB)
IF (TBB_FOUND)
  add_benchmark(tbb_hash other TBB::tbb "" "")
endif()

set(BOOST_DIR ${PARLAYHASH_SOURCE_DIR}/build/benchmarks/boost_1_83_0)

# We have to manually specify Boost's location since we are using the latest
# cutting-edge Boost version, and FindBoost.cmake can not find Boost.Unordered
# if (BOOST_DIR)
#   add_benchmark(boost_hash other "" "" "")
#   target_include_directories(boost_hash PRIVATE ${BOOST_DIR})
# endif()

set(BENCH_FILES "runtests.py" "run_graphs" "runall")

function(copy_bench_file NAME)
  file(COPY ${CMAKE_CURRENT_SOURCE_DIR}/${NAME}
    DESTINATION ${CMAKE_CURRENT_BINARY_DIR})
endfunction()

foreach(file ${BENCH_FILES})
  copy_bench_file(${file})
endforeach()

