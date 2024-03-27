#!/usr/bin/env python3
import pretty_errors
import sh
import pprintpp
pprintpp.monkeypatch()

from pprint import pprint


if __name__ == "__main__":
    pprint("recommend launch in ipython interpreter and then running step_i from root folder.")

def step_make_stage1_with_reuse():
    sh("cmake", "../../", "-DCCACHE=OFF", "-DRUNTIME_STATS=ON")
    new_env = os.environ.copy()
    new_env["RESEARCH_LEAN_COMPILER_PROFILE_CSV_PATH"] = "stage1.csv"
    new_env["RESEARCH_LOG_VERBOSE"] = "false"
    new_env["RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED"] = "true"
    sh("make", "stage2 -j20")
    sh("touch", "../../src/Init/Prelude.lean")
    sh("/usr/bin/time", "-v", "make", "stage2", "-j20")

def step_make_stage1_no_reuse():
    sh("cmake", "../../", "-DCCACHE=OFF", "-DRUNTIME_STATS=ON")
    new_env = os.environ.copy()
    new_env["RESEARCH_LEAN_COMPILER_PROFILE_CSV_PATH"] = "stage1.csv"
    new_env["RESEARCH_LOG_VERBOSE"] = "false"
    new_env["RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED"] = "false"
    sh("make", "stage2 -j20")
    sh("touch", "../../src/Init/Prelude.lean")
    sh("/usr/bin/time", "-v", "make", "stage2", "-j20")



