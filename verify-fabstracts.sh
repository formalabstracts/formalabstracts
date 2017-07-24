#!/bin/bash
set -xev
lean/build/release/shell/lean --version
lean/build/release/shell/lean meta_data.lean
