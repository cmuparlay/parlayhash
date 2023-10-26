set(SOURCES test_map.cpp)

function(add_benchmark NAME DIRECTORY LINKS OPTIONS)
  add_executable(${NAME} ${SOURCES})
  target_link_libraries(${NAME} PRIVATE parlay ${LINKS})
  target_compile_options(${NAME} PRIVATE ${OPTIONS})
  target_include_directories(${NAME} PRIVATE ${PARLAYHASH_SOURCE_DIR}/${DIRECTORY}/${NAME})
endfunction()

set(BIG_ATOMICS "wf_loadonly" "seqlock" "simplock" "wf_epoch" "wf_hazard" "wf_lowmem" "wf_daniel" "wf_indirect" "std")

foreach(NAME ${BIG_ATOMICS})
  add_executable(hash_array_${NAME} ${SOURCES})
  target_link_libraries(hash_array_${NAME} PRIVATE folly glog dl pthread double-conversion fmt gflags)
  target_link_libraries(hash_array_${NAME} PRIVATE -latomic parlay)
  target_compile_options(hash_array_${NAME} PRIVATE "-DBIG_VALUE")
  target_include_directories(hash_array_${NAME} PRIVATE ${PARLAYHASH_SOURCE_DIR}/include/hash_array)
  target_include_directories(hash_array_${NAME} PRIVATE ${PARLAYHASH_SOURCE_DIR}/include/bigatomic/${NAME})
endforeach()

set(BIG_ATOMICS_LIST "wf_loadonly" "seqlock" "simplock" "wf_epoch" "wf_indirect" "std" "wf_lowmem" "wf_daniel")

foreach(NAME ${BIG_ATOMICS_LIST})
  add_executable(hash_list_${NAME} ${SOURCES})
  target_link_libraries(hash_list_${NAME} PRIVATE folly glog dl pthread double-conversion fmt gflags)
  target_link_libraries(hash_list_${NAME} PRIVATE -latomic parlay)
  target_include_directories(hash_list_${NAME} PRIVATE ${PARLAYHASH_SOURCE_DIR}/include/hash_list_big)
  target_include_directories(hash_list_${NAME} PRIVATE ${PARLAYHASH_SOURCE_DIR}/include/bigatomic/${NAME})
endforeach()


add_benchmark(hash_nogrow include "" "")
add_benchmark(hash_grow include "" "")
add_benchmark(hash_opt include "" "-DPARLAY_USE_STD_ALLOC")
add_benchmark(hash_bytes include "" "")
add_benchmark(hash_list include "" "")
#add_benchmark(hash_daniel include "folly;glog;dl;pthread;double-conversion;fmt;gflags" "")
#add_benchmark(hash_lowmemory include "folly;glog;dl;pthread;double-conversion;fmt;gflags" "")
add_benchmark(hash_array_wf_h include "" "")

add_benchmark(hash_array_cas include "" "-DBIG_VALUE")
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


set(BENCH_FILES "runtests.py" "run_graphs" "run_paper")

function(copy_bench_file NAME)
  file(COPY ${CMAKE_CURRENT_SOURCE_DIR}/${NAME}
    DESTINATION ${CMAKE_CURRENT_BINARY_DIR})
endfunction()

foreach(file ${BENCH_FILES})
  copy_bench_file(${file})
endforeach()
