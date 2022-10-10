#!/bin/sh

pushd riscv-tests

./configure
make -j$(nproc)

popd
