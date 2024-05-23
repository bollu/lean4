#!/usr/bin/env sh
make -C /home/sb2743/24/elaboration-lean/lean4/build -j && ctest --parallel 64 --test-dir ~/24/elaboration-lean/lean4/build/stage1/
