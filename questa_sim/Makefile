MTI_HOME = /cygdrive/c/questasim64_10.4e/

VLOG = $(MTI_HOME)/win64/vlog.exe
VLIB = $(MTI_HOME)/win64/vlib.exe
VSIM = $(MTI_HOME)/win64/vsim.exe

VLOG_OPTS += -work work
VLOG_OPTS += -incr
VLOG_OPTS += -lint
VOLG_OPTS += +acc
VOLG_OPTS += -sv
VOLG_OPTS += -dpiheader dpiheader.h
VOLG_OPTS += -g
VOLG_OPTS += -O0


CSRC += ../cpp/mem_body.cpp
CSRC += ../cpp/memory_block.cpp
CSRC += ../cpp/tb_new_elf_loader.cpp
CSRC += ../cpp/tb_debug_tick.cpp

C_OBJS = $(subst .cpp,.o,$(CSRC))

all:
	$(MAKE) vlib
	$(MAKE) vlog
	$(MAKE) dpi
	$(MAKE) vsim

dpi: cimports.dll
cimports.dll: cexports.obj
	g++ -g -shared -I../cpp -fPIC $(CSRC) $(wildcard cexports.obj) -o $@ -L$(MTI_HOME)/win64 -lmtipli -lelf

.cpp.o:
	g++ -c -g $< -o $@ -fPIC -lbfd

cexports.obj:
	$(VSIM) -c $(VSIM_LIBS) -lib work $(TOP_MODULE) -dpiexportobj cexports

vlib:
	$(VLIB) work

vlog:
	$(VLOG) $(VLOG_OPTS) $(shell cat  ../vivado_sim/filelist.f)

vsim:
	vsim.exe -c work.tb -sv_lib cimports -do "run"

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
