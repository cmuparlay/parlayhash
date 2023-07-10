set(SOURCES test_map.cpp)

function(add_benchmark NAME DIRECTORY LINKS OPTIONS)
  add_executable(${NAME} ${SOURCES})
  target_link_libraries(${NAME} PRIVATE parlay ${LINKS})
  target_compile_options(${NAME} PRIVATE ${OPTIONS})
  target_include_directories(${NAME} PRIVATE ${PARLAYHASH_SOURCE_DIR}/${DIRECTORY}/${NAME})
endfunction()

add_benchmark(hash_nogrow include "" "")
add_benchmark(hash_grow include "" "")
add_benchmark(std other "" "")
add_benchmark(std_sharded other "" "")
add_benchmark(libcuckoo other "" "")
add_benchmark(growt other "" "-mcx16")

add_subdirectory(abseil-cpp)
add_benchmark(abseil other absl::flat_hash_map "")
add_benchmark(abseil_sharded other absl::flat_hash_map "")
