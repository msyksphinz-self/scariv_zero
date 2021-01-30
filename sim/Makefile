VERILATOR_OPTS =
VERILATOR_OPTS += --exe
VERILATOR_OPTS += --cc
VERILATOR_OPTS += -I../src

TOP      = mrh_tile_wrapper
FILELIST = filelist.f

all:
	verilator --top-module $(TOP) --Mdir obj_dir_riscv32 $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv32_pkg.sv -f $(FILELIST)
	verilator --top-module $(TOP) --Mdir obj_dir_riscv64 $(VERILATOR_OPTS) ../src/riscv_common_pkg.sv ../src/riscv64_pkg.sv -f $(FILELIST)

clean:
	rm -rf obj_dir_riscv32 obj_dir_riscv64
