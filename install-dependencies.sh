#!/bin/bash
set -xev
cd $TRAVIS_BUILD_DIR
mkdir lean
compile=$?
if [[ $compile == 0 ]]; then
    cd lean
    git clone https://github.com/leanprover/lean.git .
    mkdir -p build/release
    cd build/release
    cmake -DCMAKE_CXX_COMPILER=$CMAKE_CXX_COMPILER ../../src
    make -j2
fi
