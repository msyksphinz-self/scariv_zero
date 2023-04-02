#!/bin/env bash

SCARIV_DIR=/work/scariv

cd ${SCARIV_DIR}/tests/riscv-tests
./configure
make -j$(nproc)

mkdir -p ${SCARIV_DIR}/ccache/
export CCACHE_DIR=${SCARIV_DIR}/ccache/

cd ${SCARIV_DIR}/spike_dpi
make -j$(nproc)

cd ${SCARIV_DIR}/verilator_sim

isa_list=(rv32imc  rv32imfc  rv32imfdc
          rv32imac rv32imafc rv32imafdc
          rv64imc  rv64imfc  rv64imfdc
          rv64imac rv64imafc rv64imafdc)
config_list=(tiny small standard big giant)

for i in ${isa_list[@]}
do
    for c in ${config_list[@]}
    do
        ${SCARIV_DIR}/scripts/runtest.py --isa ${i} -c ${c} -t sanity -j$(nproc) --cycle 1000000 || true
    done
done
