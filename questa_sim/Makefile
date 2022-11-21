MTI_HOME = /cygdrive/c/intelFPGA/20.1/modelsim_ase/
PLATFORM = win32aloem

# MTI_HOME = /cygdrive/c/questasim64_10.4e/
# PLATFORM = win64

VLOG = $(MTI_HOME)/$(PLATFORM)/vlog.exe
VLIB = $(MTI_HOME)/$(PLATFORM)/vlib.exe
VSIM = $(MTI_HOME)/$(PLATFORM)/vsim.exe

VLOG_OPTS += -work work
VLOG_OPTS += -incr
VLOG_OPTS += -lint
VLOG_OPTS += +acc
VLOG_OPTS += +define+QUESTA_SIM=1
VLOG_OPTS += +define+SIMULATION
VLOG_OPTS += +define+DIRECT_LOAD_HEX=1
VLOG_OPTS += -sv
VLOG_OPTS += -O0
VLOG_OPTS += -l vlog.log
VLOG_OPTS += -suppress 13314,2583
FILELIST = sim_filelist.f

VLOG_OPTS += -f $(FILELIST)
# VLOG_OPTS += -R -c -do "add wave * -recursive; run -all; archive write vsim.dbar -wlf vsim.wlf ; quit;" -l sim.log +HEX=${HEX}

ISA=rv64
RV_PKG = ../src/riscv64_pkg.sv
CONFIG = standard

ifeq ($(strip $(ISA)), rv64)
	VLOG_OPTS += +define+RV64
endif

ifeq ($(strip $(ISA)), rv32)
	RV_PKG = ../src/riscv32_pkg.sv
endif

ifeq ($(strip $(CONFIG)), standard)
	CONFIG_PKG = ../src/scariv_standard_conf_pkg.sv
endif
ifeq ($(strip $(CONFIG)), big)
	CONFIG_PKG = ../src/scariv_big_conf_pkg.sv
endif
ifeq ($(strip $(CONFIG)), giant)
	CONFIG_PKG = ../src/scariv_giant_conf_pkg.sv
endif
ifeq ($(strip $(CONFIG)), small)
	CONFIG_PKG = ../src/scariv_small_conf_pkg.sv
endif
ifeq ($(strip $(CONFIG)), tiny)
	CONFIG_PKG = ../src/scariv_tiny_conf_pkg.sv
endif

all:
	$(MAKE) vlib
	$(MAKE) vlog
	$(MAKE) vsim

vlib:
	$(VLIB) work

$(FILELIST): ../src/filelist.f filelist.f
	$(shell cygpath -w -a ../tb/sim_pkg.sv > $@)
	$(shell cygpath -w -a $(RV_PKG) >> $@)
	$(shell cygpath -w -a $(CONFIG_PKG) >> $@)
	../scripts/gen_filelist.sh $^ >> $@
	sed -i 's|\\|/|g' $@

vlog:
	make -B $(FILELIST)
	$(VLOG) $(VLOG_OPTS)

vsim:
	$(VSIM)  -c work.tb -do run.tcl -l sim.log +HEX=${HEX}

clean:
	rm -rf C@
	rm -rf _info
	rm -rf cimports.dll
	rm -rf cimports.exe
	rm -rf ld.exe.stackdump
	rm -rf scariv.cr.mti
	rm -rf transcript
	rm -rf vsim_stacktrace.vstf vish_stacktrace.vstf
#	rm -rf work
