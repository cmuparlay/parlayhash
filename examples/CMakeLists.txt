add_executable(example example.cpp)
target_link_libraries(example PRIVATE parlay)
target_include_directories(example PRIVATE ${PARLAYHASH_SOURCE_DIR}/include/hash_nogrow/)

