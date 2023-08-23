#!/bin/sh

cd riscv-tests

./configure
make -j$(nproc)
