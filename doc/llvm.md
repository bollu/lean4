# LLVM Backend

The LLVM backend is an experimental compiler backend for Lean4,
which enables code generation for a variety of targets using the
[LLVM Compiler Infrastructure](https://llvm.org/).

To build the LLVM backend, perform the following steps:

1. Install `llvm-15`.
2. Build lean with the extra cmake flags:

```
CXX=clang++ CC=clang cmake -DLLVM=ON -DLLVM_CONFIG=$(which llvm-config-15)  -DCMAKE_CXX_COMPILER=$(which clang++) path/to/lean4
```

3. Use the `stage2` build of lean with the extra compiler flags:

```
$ lean --bc=<bitcode-file-name> <input.lean>
-- NOTE: the file <bitcode-file-name>.linked.bc.o is automatically created
-- by the Lean compiler.
$ leanc -o <filename>.out  <bitcode-file-name>.linked.bc.o
$ ./filename.out
```


