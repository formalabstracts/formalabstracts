set -xev
mkdir lean
compile=$?
if [[ $compile == 0 ]]; then
    cd lean
    sudo apt-get install git libgmp-dev cmake
    git clone https://github.com/leanprover/lean.git .
    mkdir -p build/release
    cd build/release
    cmake ../../src
    make
fi
