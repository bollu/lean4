set -euo pipefail

ulimit -s 8192
DIFF=diff
if diff --color --help >/dev/null 2>&1; then
    DIFF="diff --color";
fi

function fail {
    echo $1
    exit 1
}

INTERACTIVE=no
if [ $1 == "-i" ]; then
    INTERACTIVE=yes
    shift
fi
f="$1"
shift
[ $# -eq 0 ] || fail "Usage: test_single.sh [-i] test-file.lean"

function compile_lean_c_backend {
    lean --c="$f.c" "$f" || fail "Failed to compile $f into C file"
    leanc -O3 -DNDEBUG -o "$f.out" "$@" "$f.c" || fail "Failed to compile C file $f.c"
}

function compile_lean_llvm_backend {
    rm "*.ll" || true # remove debugging files.
    rm "*.bc" || true # remove bitcode files
    rm "*.o" || true # remove object files
    # print the original C program well-formatted, and LLVM sources for handy debugging.
    lean --c="$f.c" "$f" || fail "Failed to compile $f into C file"
    clang-format -i "$f.c"
    clang $(leanc --print-cflags) -S -emit-llvm "$f.c" -o "$f.c.ll" # generate ll.
    sed -i "s/optnone//g" "$f.c.ll" # remove optnone to actually allow some optimisation.
    opt -S -O2 "$f.c.ll" -o "$f.c.o2.ll" # optimise it a little to be much more readable.

    # TODO: find a sane way to pick this path up, similar to the way leanc hardcodes these paths via flags with --print-cflags
    # Also, this should be in stage0, since we want it to be present in all circumstances.
    echo "using lean: $(which lean); leanc: $(which leanc)"
    # export LIBRUNTIMEBC=$(git rev-parse --show-toplevel)/build/stage1/runtime/libleanrt.bc # TODO: get this information into `leanc`.
    set -o xtrace
    # lean --bc="$f.bc" "$f" || fail "Failed to compile $f into bitcode file"
    # opt -S "$f.bc" -o "$f.bc.ll" # generate easy to read ll from bitcode.
    # opt -S -O2 "$f.bc.ll" -o "$f.bc.o2.ll" # generate easy to read ll from bitcode.
    # llvm-link "$f.bc" $LIBRUNTIMEBC -o "$f.linked.bc"
    lean --bc="$f.linked.bc" "$f" || fail "Failed to compile $f into bitcode file"
    opt -S -O2 "$f.linked.bc" -o "$f.linked.bc.o2.ll" # generate easy to read ll from bitcode
    # llc --relocation-model=pic -O1 -march=x86-64 -filetype=obj "$f.linked.bc" -o "$f.o" # TODO: figure out how to pick up triple.
    leanc -o "$f.out" "$@" "$f.linked.bc.o" || fail "Failed to link object file '$f.o', generated from bitcode file $f.linked.bc"
}

function exec_capture {
    # mvar suffixes like in `?m.123` are deterministic but prone to change on minor changes, so strip them
    LEAN_BACKTRACE=0 "$@" 2>&1 | perl -pe 's/(\?(\w|_\w+))\.[0-9]+/\1/g' > "$f.produced.out"
}

# Remark: `${var+x}` is a parameter expansion which evaluates to nothing if `var` is unset, and substitutes the string `x` otherwise.
function exec_check {
    ret=0
    [ -n "${expected_ret+x}" ] || expected_ret=0
    [ -f "$f.expected.ret" ] && expected_ret=$(< "$f.expected.ret")
    exec_capture "$@" || ret=$?
    if [ -n "$expected_ret" ] && [ $ret -ne $expected_ret ]; then
        echo "Unexpected return code $ret executing '$@'; expected $expected_ret. Output:"
        cat "$f.produced.out"
        exit 1
    fi
}

function diff_produced {
    if test -f "$f.expected.out"; then
        if $DIFF -au --strip-trailing-cr -I "executing external script" "$f.expected.out" "$f.produced.out"; then
            :
        else
            echo "ERROR: file $f.produced.out does not match $f.expected.out"
            if [ $INTERACTIVE == "yes" ]; then
                meld "$f.produced.out" "$f.expected.out"
                if diff -I "executing external script" "$f.expected.out" "$f.produced.out"; then
                    echo "-- mismatch was fixed"
                fi
            fi
            exit 1
        fi
    else
        echo "ERROR: file $f.expected.out does not exist"
        if [ $INTERACTIVE == "yes" ]; then
            read -p "copy $f.produced.out (y/n)? "
            if [ $REPLY == "y" ]; then
                cp -- "$f.produced.out" "$f.expected.out"
                echo "-- copied $f.produced.out --> $f.expected.out"
            fi
        fi
        exit 1
    fi
}
