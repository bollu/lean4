#!/usr/bin/env bash
# Script to check the delta between the C and LLVM versions
source ../common.sh

# First check the C version actually works...
echo "running C program..."
rm "./$f.out" || true
compile_lean_c_backend
exec_check "./$f.out"
cp "$f.produced.out" "$f.expected.out"
diff_produced

# Then check the LLVM version
echo "running LLVM program..."
rm "./$f.out" || true
compile_lean_llvm_backend
exec_check "./$f.out"
diff_produced
