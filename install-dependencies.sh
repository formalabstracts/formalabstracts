#!/bin/bash
set -xev
if [[ ! -d ../lean ]]; then
    mkdir ../lean
    cd ../lean
    git clone https://github.com/leanprover/lean.git .
    mkdir -p build/release
    cd build/release
    cmake -DCMAKE_CXX_COMPILER=$CMAKE_CXX_COMPILER ../../src
    make -j2
fi
