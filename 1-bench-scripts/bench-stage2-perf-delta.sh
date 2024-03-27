#!/usr/bin/env bash
set -e
set -o xtrace


git clean --dry-run ../

read -r -p "Do you want to proceed? (y/n): " answer

case $answer in
  [Yy]* ) echo "Continuing."; ;;
  [Nn]* ) echo "Quitting"; exit 0 ;;
  * ) echo "Invalid input."; exit 1;;
esac

# redirect all output to log file, plus data.
exec > >(tee -a "$0.log") 2>&1

# git clean -xf ../
# git checkout 834d0b2c328bf765debcc1f7feac11bee294b083 # checkout a particular commit.

cd ../
rm -rf build
mkdir build
cd build

rm -rf *
cmake ../../ -DCCACHE=OFF -DRUNTIME_STATS=ON
export RESEARCH_LOG_VERBOSE=false
unset RESEARCH_LEAN_COMPILER_PROFILE_CSV_PATH
export RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED=true
make -j20 stage2
touch ../../src/Init/Prelude.lean
export RESEARCH_LEAN_COMPILER_PROFILE_CSV_PATH = stage1.reuse.enabled.csv
/usr/bin/time -V make -j20 stage2 | tee -a "stage2.log"

rm -rf *
cmake ../../ -DCCACHE=OFF -DRUNTIME_STATS=ON
export RESEARCH_LOG_VERBOSE=false
unset RESEARCH_LEAN_COMPILER_PROFILE_CSV_PATH
export RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED=false
make -j20 stage2
touch ../../src/Init/Prelude.lean
export RESEARCH_LEAN_COMPILER_PROFILE_CSV_PATH = stage1.reuse.disabled.csv
/usr/bin/time -V make -j20 stage2 | tee -a "stage2.log"
