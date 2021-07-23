#!/usr/bin/env bash
# ./src/config.h.in
# ./build/stage0/include/lean/config.h
set -o xtrace
set -e 

FILES=$(ls -1u *.cpp)
LLFILES=""
LEANCC="clang -I $HOME/work/lean4/build/stage0/include -I $HOME/work/lean4/src/"

for file in $FILES; do 
    i=$(basename $file .cpp)
    LLFILES="$LLFILES $i.ll"
    $LEANCC -O3 $file -S -emit-llvm  -o  $i.ll
done

echo $LLFILES

# $LEANCC -O3 allocprof.cpp -S -emit-llvm -o allocprof.ll
# $LEANCC -O3 apply.cpp -S -emit-llvm -o apply.ll 
# $LEANCC -O3 compact.cpp -S -emit-llvm -o compact.ll
# $LEANCC -O3 debug.cpp -S -emit-llvm -o debug.ll
# $LEANCC -O3 exception.cpp -S -emit-llvm -o exception.ll
# $LEANCC -O3 hash.cpp -S -emit-llvm -o hash.ll
# $LEANCC -O3 init_module.cpp -S -emit-llvm -o init_module.ll
# $LEANCC -O3 interrupt.cpp -S -emit-llvm -o interrupt.ll
# $LEANCC -O3 io.cpp -S -emit-llvm -o io.ll
# io.cpp
# memory.cpp
# mpq.cpp
# mpz.cpp
# $LEANCC -O3 object.cpp -S -emit-llvm -o object.ll 
# platform.cpp
# process.cpp
# serializer.cpp
# sharecommon.cpp
# stackinfo.cpp
# stack_overflow.cpp
# thread.cpp
# utf8.cpp

llvm-link $LLFILES -S -o runtime.ll
# alwaysinline causes runtime to take infinite amounts of time.
sed -i s/noinline/alwaysinline/g runtime.ll
# sed -i s/noinline//g runtime.ll
sed -i s/optnone//g runtime.ll
opt -S -O3 runtime.ll -o runtime-optimized.ll
mv runtime-optimized.ll runtime.ll
cp ~/work/lean4/src/runtime/runtime.ll ~/work/lz/lean-linking-incantations/lib-runtime
