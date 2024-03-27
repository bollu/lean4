#!/usr/bin/env bash
set -e
set -o xtrace


RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED=TRUE lean $1 -c $(basename $1 .lean).reuse.enabled.c
RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED=FALSE lean $1 -c $(basename $1 .lean).reuse.disabled.c
leanc $(basename $1 .lean).reuse.enabled.c -o $(basename $1 .lean).reuse.enabled.out
leanc $(basename $1 .lean).reuse.disabled.c -o $(basename $1 .lean).reuse.disabled.out

/usr/bin/time -v ./$(basename $1 .lean).reuse.disabled.out $2
/usr/bin/time -v ./$(basename $1 .lean).reuse.enabled.out $2
