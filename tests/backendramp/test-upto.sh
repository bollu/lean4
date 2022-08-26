#!/usr/bin/env bash
# Quick shell script to run the lean tests upto a specified limit (inclusive). 
# Usage: ./test-upto.sh 5 (to run tests [1, 2, 3, 4, 5])
set -e

for i in $(seq 1 $1); do
    ls $i-*.lean
    PATH=/home/bollu/work/lean-llvm/lean4/build/stage1/bin:$PATH ./test_single.sh $i-*.lean
done;

