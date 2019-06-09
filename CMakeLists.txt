cmake_minimum_required(VERSION 3.10)

# Make PROJECT_SOURCE_DIR, PROJECT_BINARY_DIR, and PROJECT_NAME available.
set(PROJECT_NAME AlgebraProject)
project(${PROJECT_NAME})

include("${CMAKE_BINARY_DIR}/conanbuildinfo.cmake")
conan_basic_setup(TARGETS NO_OUTPUT_DIRS)

set(CMAKE_CXX_FLAGS "-g -Wall -std=c++17 -pthread")

if (APPLE)
	add_definitions(-DGTEST_USE_OWN_TR1_TUPLE)
	add_definitions(-D__GLIBCXX__)
endif (APPLE)

enable_testing()

add_executable(runAttack bleichenbacher_attack.cpp )

target_link_libraries(runAttack CONAN_PKG::gtest)
target_link_libraries(runAttack CONAN_PKG::cryptopp)
