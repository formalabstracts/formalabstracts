#!/bin/bash
set -xev
lean/bin/lean --version
lean/bin/leanpkg configure
lean/bin/lean --make
