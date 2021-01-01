VERILATOR_OPTS =
VERILATOR_OPTS += --exe
VERILATOR_OPTS += --cc
VERILATOR_OPTS += -I../src

FILELIST = filelist.f

all:
	verilator $(VERILATOR_OPTS) -f $(FILELIST)
