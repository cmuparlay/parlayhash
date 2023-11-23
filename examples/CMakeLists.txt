add_executable(example example.cpp)
target_link_libraries(example PRIVATE parlay)
target_include_directories(example PRIVATE ${PARLAYHASH_SOURCE_DIR}/include/hash_nogrow/)

add_executable(upsert_example upsert_example.cpp)
target_link_libraries(upsert_example PRIVATE parlay)
target_include_directories(upsert_example PRIVATE ${PARLAYHASH_SOURCE_DIR}/include/hash_nogrow/)

add_executable(upsert_example_grow upsert_example.cpp)
target_link_libraries(upsert_example_grow PRIVATE parlay)
target_include_directories(upsert_example_grow PRIVATE ${PARLAYHASH_SOURCE_DIR}/include/hash_grow/)

