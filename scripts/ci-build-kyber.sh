#!/usr/bin/env bash

./c.sh
cd c
cmake \
  -DCMAKE_EXE_LINKER_FLAGS="-fuse-ld=mold" \
  -DCMAKE_SHARED_LINKER_FLAGS="-fuse-ld=mold" \
  -G "Ninja Multi-Config" -B build
cmake --build build --config Release
