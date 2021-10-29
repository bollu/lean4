#!/usr/bin/env bash
# ./src/config.h.in
# ./build/stage0/include/lean/config.h
set -o xtrace
set -e 

rm runtime.ll || true
LEANCC="clang -O3 -DLEAN_MULTI_THREAD -I $HOME/work/lean4/build/release/stage0/include -I $HOME/work/lean4/src/"
$LEANCC -O3 alloc.cpp -S -emit-llvm -o alloc.ll 
$LEANCC -O3 object.cpp -S -emit-llvm -o object.ll 
$LEANCC -O3 apply.cpp -S -emit-llvm -o apply.ll 
$LEANCC -O3 thread.cpp -S -emit-llvm -o thread.ll 
llvm-link alloc.ll object.ll apply.ll thread.ll -S -o runtime.ll
# alwaysinline causes runtime to take infinite amounts of time.
sed -i s/noinline/alwaysinline/g runtime.ll
# sed -i s/noinline//g runtime.ll
sed -i s/optnone//g runtime.ll
opt -S -O3 runtime.ll -o runtime-optimized.ll
mv runtime-optimized.ll runtime.ll
cp ~/work/lean4/src/runtime/runtime.ll ~/work/lz/lean-linking-incantations/lib-runtime
