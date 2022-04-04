REGRESSION_LIST += rv32imc_small_test
REGRESSION_LIST += rv32imfc_small_test
REGRESSION_LIST += rv32imfdc_small_test
REGRESSION_LIST += rv64imc_small_test
REGRESSION_LIST += rv64imfc_small_test
REGRESSION_LIST += rv64imfdc_small_test
REGRESSION_LIST += rv64imc_small_benchmarks
REGRESSION_LIST += rv64imfc_small_benchmarks
REGRESSION_LIST += rv64imfdc_small_benchmarks
REGRESSION_LIST += rv64imc_small_aapg
REGRESSION_LIST += rv64imfc_small_aapg
REGRESSION_LIST += rv64imfdc_small_aapg

#
# RV32
#
rv32imc_small: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=small ISA=imc RV_XLEN=32 RV_FLEN=0

rv32imfc_small: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=small ISA=imfc RV_XLEN=32 RV_FLEN=32

rv32imfdc_small: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=small ISA=imfdc RV_XLEN=32 RV_FLEN=64

rv32imc_small_test:
	$(MAKE) rv32imc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imc_small rv32-tests.json log_rv32imc_small $(NPROCS) 2>&1 | tee rv32imc_small_test.log

rv32imfc_small_test:
	$(MAKE) rv32imfc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imfc_small rv32-tests.json log_rv32imfc_small $(NPROCS) 2>&1 | tee rv32imfc_small_test.log

rv32imfdc_small_test:
	$(MAKE) rv32imfdc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imfdc_small rv32-tests.json log_rv32imfdc_small $(NPROCS) 2>&1 | tee rv32imfdc_small_test.log


#
# RV64
#
rv64imc_small: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=small ISA=imc RV_XLEN=64 RV_FLEN=0

rv64imfc_small: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=small ISA=imfc RV_XLEN=64 RV_FLEN=32

rv64imfdc_small: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=small ISA=imfdc RV_XLEN=64 RV_FLEN=64

rv64imc_small_test:
	$(MAKE) rv64imc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_small rv64-tests.json log_rv64imc_small $(NPROCS) 2>&1 | tee rv64imc_small_test.log

rv64imfc_small_test:
	$(MAKE) rv64imfc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_small rv64-tests.json log_rv64imfc_small $(NPROCS) 2>&1 | tee rv64imfc_small_test.log

rv64imfdc_small_test:
	$(MAKE) rv64imfdc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_small rv64-tests.json log_rv64imfdc_small $(NPROCS) 2>&1 | tee rv64imfdc_small_test.log

rv64imc_small_benchmarks:
	$(MAKE) rv64imc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_small rv64-bench.json log_rv64imc_small $(NPROCS) 2>&1 | tee rv64imc_small_benchmark.log

rv64imfc_small_benchmarks:
	$(MAKE) rv64imfc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_small rv64-bench.json log_rv64imfc_small $(NPROCS) 2>&1 | tee rv64imfc_small_benchmark.log

rv64imfdc_small_benchmarks:
	$(MAKE) rv64imfdc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_small rv64-bench.json log_rv64imfdc_small $(NPROCS) 2>&1 | tee rv64imfdc_small_benchmark.log

rv64imc_small_aapg:
	$(MAKE) rv64imc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_small     ../tests/aapg.json log_rv64imc_small_aapg  	  $(NPROCS) 2>&1 | tee rv64imc_small_aapg.log

rv64imfc_small_aapg:
	$(MAKE) rv64imfc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_small     ../tests/aapg.json log_rv64imfc_small_aapg  	  $(NPROCS) 2>&1 | tee rv64imfc_small_aapg.log

rv64imfdc_small_aapg:
	$(MAKE) rv64imfdc_small DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_small     ../tests/aapg.json log_rv64imfdc_small_aapg	  $(NPROCS) 2>&1 | tee rv64imfdc_small_aapg.log
