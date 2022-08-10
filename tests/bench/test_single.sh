#!/usr/bin/env bash
source ../common.sh

compile_lean_c_backend
exec_check "./$f.out" $(cat "$f.args")
diff_produced

compile_lean_llvm_backend
exec_check "./$f.out" $(cat "$f.args")
diff_produced
