set(SOURCES test_map.cpp)

function(add_benchmark NAME DIRECTORY LINKS OPTIONS)
  add_executable(${NAME} ${SOURCES})
  target_link_libraries(${NAME} PRIVATE parlay ${LINKS})
  target_compile_options(${NAME} PRIVATE ${OPTIONS})
  target_include_directories(${NAME} PRIVATE ${PARLAYHASH_SOURCE_DIR}/${DIRECTORY}/${NAME})
endfunction()

add_benchmark(hash_nogrow include "" "")
add_benchmark(hash_grow include "" "")
add_benchmark(hash_opt include "" "")
add_benchmark(hash_opt2 include "" "")
add_benchmark(hash_opt3 include "" "")
add_benchmark(std_hash other "" "")
add_benchmark(std_sharded other "" "")
add_benchmark(libcuckoo other "" "")
add_benchmark(growt other "" "-mcx16")

find_package(GTest)
find_package(absl)
#add_subdirectory(abseil-cpp)
if (absl_FOUND)
  add_benchmark(abseil other absl::flat_hash_map "")
  add_benchmark(abseil_sharded other absl::flat_hash_map "")
endif()

find_package(folly)
if (folly_FOUND)
  add_benchmark(folly_hash other "folly;glog;dl;pthread;double-conversion;fmt;gflags" "")
endif()

find_package(TBB)
IF (TBB_FOUND)
  add_benchmark(tbb_hash other TBB::tbb "")
endif()


