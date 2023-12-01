RV_DEFINE += RV64
RV_DEFINE += RV_AMO=1
export RV_DEFINE
export RV_FILE = riscv64_pkg.sv
export CONF_FILE = scariv_boomv3_conf_pkg.sv
export FPU_FILE = riscv_fpu_imafdc_pkg.sv
export VPU_FILE = riscv_vec_v512_d128_conf_pkg.sv
