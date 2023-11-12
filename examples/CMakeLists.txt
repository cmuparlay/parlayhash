add_executable(example example.cpp)
target_link_libraries(example PRIVATE parlay)
target_include_directories(example PRIVATE ${PARLAYHASH_SOURCE_DIR}/include/hash_nogrow/)

add_executable(example2 example2.cpp)
target_link_libraries(example2 PRIVATE parlay)
target_include_directories(example2 PRIVATE ${PARLAYHASH_SOURCE_DIR}/include/hash_nogrow/)

