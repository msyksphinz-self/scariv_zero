#!/bin/sh

NUM_GEN=99
DATE=`date +%Y%m%d_%H%M%S`

mkdir -p $DATE

for dir_num in `seq -w 0 $NUM_GEN`
do
    mkdir -p $DATE/${dir_num}/
    make -C ../riscv-torture/
    mv ../riscv-torture/output/test.S $DATE/${dir_num}/
    ln -s ../../../riscv-torture/env/p/riscv_test.h $DATE/${dir_num}/
    ln -s ../../../common/common.mk $DATE/${dir_num}/Makefile
    make -C $DATE/${dir_num}/
done
