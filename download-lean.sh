cd /lean
git clone --depth=50 https://github.com/leanprover/lean.git .
mkdir -p build/release
cd build/release
cmake -DCMAKE_CXX_COMPILER=$CMAKE_CXX_COMPILER ../../src
make -j2
