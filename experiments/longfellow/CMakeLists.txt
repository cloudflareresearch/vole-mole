# Builds the Longfellow blind signature benchmark against a checkout of
# https://github.com/google/longfellow-zk. See README.md.

cmake_minimum_required(VERSION 3.13)
project(longfellow_blindsig CXX)

set(LONGFELLOW_DIR "" CACHE PATH "Path to a checkout of longfellow-zk")
if (NOT EXISTS "${LONGFELLOW_DIR}/lib/CMakeLists.txt")
  message(FATAL_ERROR "Set LONGFELLOW_DIR to a checkout of longfellow-zk")
endif()

add_subdirectory("${LONGFELLOW_DIR}/lib" longfellow EXCLUDE_FROM_ALL)

# Longfellow sets these up in its own directory scope only.
find_package(benchmark REQUIRED)
if (APPLE)
  include_directories("/opt/homebrew/include")
  link_directories("/opt/homebrew/lib")
endif()
string(TOLOWER "${CMAKE_SYSTEM_PROCESSOR}" ARCHITECTURE)
if (ARCHITECTURE MATCHES "x86_64")
  add_compile_options(-mpclmul)
elseif (ARCHITECTURE MATCHES "arm64" AND APPLE)
  add_compile_options(-mcpu=apple-m1 -march=armv8-a+crypto)
elseif (ARCHITECTURE MATCHES "aarch64|arm64")
  add_compile_options(-march=armv8-a+crypto)
endif()

add_compile_definitions(OPENSSL_SUPPRESS_DEPRECATED=1)
add_executable(longfellow_blindsig longfellow_blindsig.cc)
target_include_directories(longfellow_blindsig PRIVATE "${LONGFELLOW_DIR}/lib")
target_link_libraries(longfellow_blindsig algebra util benchmark::benchmark)
