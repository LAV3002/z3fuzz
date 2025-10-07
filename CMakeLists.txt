cmake_minimum_required(VERSION 3.22)

project(Z3FUZZ VERSION 0.0.1 LANGUAGES CXX)

# set(AFL_PATH /home/laver/ispras_mag/test_task/AFL)

# set(CMAKE_C_COMPILER ${AFL_PATH}/afl-gcc)
# set(CMAKE_CXX_COMPILER ${AFL_PATH}/afl-g++)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(Z3_BUILD_EXECUTABLE ON)

add_subdirectory(z3)