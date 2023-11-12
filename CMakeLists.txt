cmake_minimum_required(VERSION 3.22)
project(proof2prog)

set(CMAKE_CXX_STANDARD 20)

add_executable(proof2prog main.cpp
        algorithm.h
        Types.h
        Terms.h
        param.h
        coq_proof.h
)

add_executable(tests tests.cpp)