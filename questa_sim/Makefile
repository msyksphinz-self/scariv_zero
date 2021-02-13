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
VLOG_OPTS += -sv
VLOG_OPTS += -O0
VLOG_OPTS += +define+DIRECT_LOAD_HEX

FILELIST = sim_filelist.f

C_OBJS = $(subst .cpp,.o,$(CSRC))

all:
	$(MAKE) vlib
	$(MAKE) vlog
	$(MAKE) vsim

vlib:
	$(VLIB) work

$(FILELIST): ../src/filelist.f filelist.f
	cat $^ > $@

vlog: $(FILELIST)
	$(VLOG) $(VLOG_OPTS) ../src/riscv64_pkg.sv $(shell cat $^)

vsim:
	$(VSIM)  -c work.tb -do "add wave * -recursive; run -all; archive write vsim.dbar -wlf vsim.wlf ; quit;" -l sim.log

clean:
	rm -rf $(C_OBJS)
	rm -rf _info
	rm -rf cimports.dll
	rm -rf cimports.exe
	rm -rf ld.exe.stackdump
	rm -rf msrh.cr.mti
	rm -rf transcript
	rm -rf vsim_stacktrace.vstf
	rm -rf work
