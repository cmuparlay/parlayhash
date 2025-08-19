cmake_minimum_required(VERSION 3.13)
project(PARLAYHASH VERSION 1.0 DESCRIPTION "Lock-Free Locks" LANGUAGES CXX)

# Set a default build type
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE "Release" CACHE STRING "Build type (Debug Release RelWithDebInfo MinSizeRel)" FORCE)
  message(STATUS "No build type specified. Defaulted to RELEASE.")
  message(STATUS "To specify a build type, add -DCMAKE_BUILD_TYPE=<DEBUG/RELEASE/RELWITHDEBINFO/MINSIZEREL>")
endif(NOT CMAKE_BUILD_TYPE)
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g -fno-omit-frame-pointer")

message(STATUS "--------------- General configuration -------------")
message(STATUS "CMake Generator:                ${CMAKE_GENERATOR}")
message(STATUS "Compiler:                       ${CMAKE_CXX_COMPILER_ID} ${CMAKE_CXX_COMPILER_VERSION}")
message(STATUS "Build type:                     ${CMAKE_BUILD_TYPE}")
message(STATUS "CMAKE_CXX_FLAGS:                ${CMAKE_CXX_FLAGS}")
message(STATUS "CMAKE_CXX_FLAGS_DEBUG:          ${CMAKE_CXX_FLAGS_DEBUG}")
message(STATUS "CMAKE_CXX_FLAGS_RELEASE:        ${CMAKE_CXX_FLAGS_RELEASE}")
message(STATUS "CMAKE_CXX_FLAGS_RELWITHDEBINFO: ${CMAKE_CXX_FLAGS_RELWITHDEBINFO}")
message(STATUS "CMAKE_EXE_LINKER_FLAGS          ${CMAKE_EXE_LINKER_FLAGS}")
message(STATUS "CMAKE_INSTALL_PREFIX:           ${CMAKE_INSTALL_PREFIX}" )

# set(CMAKE_CXX_CLANG_TIDY
#   clang-tidy;
#   -format-style='file';
#   -header-filter=${CMAKE_CURRENT_SOURCE_DIR};
# )

# -------------------------------------------------------------------
#                       Library definition

set(PARLAYHASH_INCLUDE_DIR "${PARLAYHASH_SOURCE_DIR}/include")
#set(CMAKE_CXX_COMPILER "/usr/bin/g++-11")
#set(CMAKE_CXX_COMPILER "/usr/bin/clang++-16")

add_library(parlay INTERFACE)
target_include_directories(parlay INTERFACE ${PARLAYHASH_INCLUDE_DIR})
target_compile_features(parlay INTERFACE cxx_std_17)
target_compile_options(parlay INTERFACE -g)

# Find threading library
find_package(Threads REQUIRED)
target_link_libraries(parlay INTERFACE Threads::Threads)

add_subdirectory(benchmarks)

add_subdirectory(examples)

message(STATUS "---------------------------------- Unit Tests ----------------------------------")

# User option to build unit tests
option(PARLAYHASH_TEST  "Build unit tests"       OFF)

if (PARLAYHASH_TEST)
  # Set CMake options for GoogleTest
  set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
  set(INSTALL_GTEST OFF CACHE BOOL "" FORCE)
  set(BUILD_GMOCK OFF CACHE BOOL "" FORCE)
  set(gtest_disable_pthreads ON CACHE BOOL "" FORCE)

  # Download and configure GoogleTest
  include(FetchContent)
  FetchContent_Declare(googletest
    GIT_REPOSITORY  https://github.com/google/googletest.git
    GIT_TAG         main
  )
  FetchContent_GetProperties(googletest)
  if(NOT googletest_POPULATED)
    message(STATUS "testing: Configuring GoogleTest")
    FetchContent_Populate(googletest)  
    set(CMAKE_SUPPRESS_DEVELOPER_WARNINGS 1 CACHE BOOL "")
    add_subdirectory(${googletest_SOURCE_DIR}
                     ${googletest_BINARY_DIR}
                     EXCLUDE_FROM_ALL)
  endif()

  # Include test targets
  message(STATUS "testing: Enabled")
  include(CTest)
  add_subdirectory(test)

else()
  message(STATUS "testing: Disabled (enable with -DPARLAYHASH_TEST=On)")
endif()
