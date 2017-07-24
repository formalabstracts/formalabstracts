set -xev
mkdir lean
compile=$?
if [[ $compile == 0 ]]; then
    cd lean
    git clone https://github.com/leanprover/lean.git .
    mkdir -p build/release
    cd build/release
    cmake ../../src
    make
fi
