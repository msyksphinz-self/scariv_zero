# export SNPSLMD_LICENSE_FILE=1700@133.11.58.5
# export VCS_HOME   = /home/shioya/opt/cad/synopsys/vcs/U-2023.03
export VERDI_HOME = /home/shioya/opt/cad/synopsys/verdi/T-2022.06-SP1-1/
# export LD_LIBRARY_PATH = $(VCS_HOME)linux64/lib/:$(VERDI_HOME)share/PLI/VCS/linux64/:$(VCS_HOME)platform/linux64/bin/:$(shell echo $$LD_LIBRARY_PATH):

ISA = imfdc
CONF = standard

VCS_OPTS += +define+VCS_SIM

VCS_OPTS += -full64
VCS_OPTS += -sverilog
VCS_OPTS += +define+RV64
VCS_OPTS += +define+RV_AMO=1
VCS_OPTS += +define+SIMULATION
VCS_OPTS += -l compile.log
VCS_OPTS += +incdir+../include/
VCS_OPTS += +incdir+../src
VCS_OPTS += +incdir+../src/fpnew/src/common_cells/include
VCS_OPTS += +incdir+../tb
VCS_OPTS += ../src/riscv_common_pkg.sv
VCS_OPTS += ../src/riscv_fpu_$(ISA)_pkg.sv
VCS_OPTS += ../src/riscv64_pkg.sv
VCS_OPTS += ../configs/scariv_$(CONF)_conf_pkg.sv
VCS_OPTS += ../src/riscv_vec_v512_d128_conf_pkg.sv
VCS_OPTS += ../cpp/tb_elf_loader.cpp
VCS_OPTS += -f $(FILELIST)
VCS_OPTS += -o simv
VCS_OPTS += -top tb
VCS_OPTS += -full64
VCS_OPTS += -debug_access+all
# VCS_OPTS += -kdb
VCS_OPTS += -P $(VERDI_HOME)/share/PLI/VCS/LINUX64/novas.tab
VCS_OPTS += $(VERDI_HOME)/share/PLI/VCS/LINUX64/pli.a

VCS_OPTS += $(abspath ../cpp/tb_debug_tick.cpp)
VCS_OPTS += $(abspath ../cpp/memory_block.cpp)
VCS_OPTS += $(abspath ../cpp/mem_body.cpp)
VCS_OPTS += $(abspath ../cpp/kanata.cpp)
VCS_OPTS += $(abspath ../spike_dpi/spike_dpi.cpp)
VCS_OPTS += $(abspath ./libsoftfloat.a)

VCS_OPTS += -CFLAGS "-I"$(abspath ../spike_dpi/riscv-isa-sim/)
VCS_OPTS += -CFLAGS "-I"$(abspath ../spike_dpi/riscv-isa-sim/riscv)
VCS_OPTS += -CFLAGS "-I"$(abspath ../spike_dpi/riscv-isa-sim/softfloat/)
VCS_OPTS += -CFLAGS "-I"$(abspath ../cpp)
VCS_OPTS += -CFLAGS "-I"$(abspath ../spike_dpi)
VCS_OPTS += -LDFLAGS "-L"$(abspath ../spike_dpi/riscv-isa-sim/)

VCS_OPTS += $(abspath ../spike_dpi/riscv-isa-sim)/libspike_main.a
VCS_OPTS += $(abspath ../spike_dpi/riscv-isa-sim)/libriscv.a
VCS_OPTS += $(abspath ../spike_dpi/riscv-isa-sim)/libdisasm.a
VCS_OPTS += $(abspath ../spike_dpi/riscv-isa-sim)/libsoftfloat.a
VCS_OPTS += $(abspath ../spike_dpi/riscv-isa-sim)/libfesvr.a
VCS_OPTS += $(abspath ../spike_dpi/riscv-isa-sim)/libfdt.a

VERDI_OPTS += -2012
VERDI_OPTS += -simflow
VERDI_OPTS += -full64
VERDI_OPTS += -nologo
VERDI_OPTS += -top tb
VERDI_OPTS += -ssf wave.fsdb
VERDI_OPTS += -vcs simv
VERDI_OPTS += +define+RV64
VERDI_OPTS += +define+RV_AMO=1
VERDI_OPTS += +define+SIMULATION
VERDI_OPTS += -l compile.log
VERDI_OPTS += +incdir+../include/
VERDI_OPTS += +incdir+../src
VERDI_OPTS += +incdir+../src/fpnew/src/common_cells/include
VERDI_OPTS += +incdir+../tb
VERDI_OPTS += ../src/riscv_common_pkg.sv
VERDI_OPTS += ../src/riscv_fpu_$(ISA)_pkg.sv
VERDI_OPTS += ../src/riscv64_pkg.sv
VERDI_OPTS += ../configs/scariv_$(CONF)_conf_pkg.sv
VERDI_OPTS += -f sim_filelist.f

FILELIST = sim_filelist.f

all: build
	mkdir -p sim_rv64imafdc_standard/dhrystone && cd sim_rv64imafdc_standard/dhrystone && \
	../../simv +fsdb+all +fsdb+autoflush +ELF=../../../tests/riscv-tests/benchmarks/dhrystone.riscv 2>&1 | tee sim.log
	fsdb2vcd sim_rv64imafdc_standard/dhrystone/wave.fsdb | bzip2 > sim_rv64imafdc_standard/dhrystone/wave.bz2

build: $(FILELIST)
	${VCS_HOME}/bin/vcs $(VCS_OPTS)

#	$(MAKE) -C ../verilator_sim/ RV_FLEN=64 .config_design_xlen64_flen64

$(FILELIST): ../src/fpnew.vf ../src/filelist.vf filelist.f
	echo "../tb/sim_pkg.sv" > $@
	cat $^ >> $@

verdi:
	$(VERDI_HOME)/bin/verdi $(VERDI_OPTS)

clean:
	rm -rf csrc *.log simv* vc_hdrs.h ucli.key sim_filelist.f wave.fsdb verdiLog novas.*
