#!/usr/bin/env bash
source ../common.sh

compile_lean_c_backend
cp ./qsort.lean.out ./qsort.lean.out.c
# Then check the LLVM version
if lean_has_llvm_support; then
  echo "running LLVM program..."
  compile_lean_llvm_backend
  cp ./qsort.lean.out ./qsort.lean.out.llvm
fi

opt -O3 qsort.lean.ll -S | grep define > c.out
opt qsort.lean.linked.bc -S -O3 | grep define  > ll.out 
