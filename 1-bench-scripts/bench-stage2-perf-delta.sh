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

git clean -xf ../

git checkout 834d0b2c328bf765debcc1f7feac11bee294b083 # checkout a particular commit.

cd ../
rm -rf build
mkdir build
cd build
cmake ../ -DCCACHE=OFF -DRUNTIME_STATS=ON

make -j stage2

export RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED=TRUE
export RESEARCH_LOG_VERBOSE=FALSE
touch ../src/Init/Prelude.lean
time -v make -j stage2

export RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED=FALSE
export RESEARCH_LOG_VERBOSE=FALSE
touch ../src/Init/Prelude.lean
time -v make -j stage2

# make -j stage3
# touch ../src/Init/Prelude.lean
# make -j stage3
#
# touch ../src/Init/Prelude.lean
