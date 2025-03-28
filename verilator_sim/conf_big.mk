REGRESSION_LIST += rv32imc_big_test
REGRESSION_LIST += rv32imfc_big_test
REGRESSION_LIST += rv32imfdc_big_test
REGRESSION_LIST += rv64imc_big_test
REGRESSION_LIST += rv64imfc_big_test
REGRESSION_LIST += rv64imfdc_big_test
REGRESSION_LIST += rv64imc_big_benchmarks
REGRESSION_LIST += rv64imfc_big_benchmarks
REGRESSION_LIST += rv64imfdc_big_benchmarks
REGRESSION_LIST += rv64imc_big_aapg
REGRESSION_LIST += rv64imfc_big_aapg
REGRESSION_LIST += rv64imfdc_big_aapg

#
# RV32
#
rv32imc_big: $(FILELIST) .config_design_xlen32_flen$(RV_FLEN)
#	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=big ISA=imc RV_XLEN=32 RV_FLEN=0 > $@_build.log 2>&1

rv32imfc_big: $(FILELIST) .config_design_xlen32_flen$(RV_FLEN)
#	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=big ISA=imfc RV_XLEN=32 RV_FLEN=32 > $@_build.log 2>&1

rv32imfdc_big: $(FILELIST) .config_design_xlen32_flen$(RV_FLEN)
#	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=big ISA=imfdc RV_XLEN=32 RV_FLEN=64 > $@_build.log 2>&1

rv32imc_big_test:
	$(MAKE) rv32imc_big DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb scariv_tb_rv32imc_big rv32-tests.json log_rv32imc_big $(NPROCS) 2>&1 | tee rv32imc_big_test.log

rv32imfc_big_test:
	$(MAKE) rv32imfc_big DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb scariv_tb_rv32imfc_big rv32-tests.json log_rv32imfc_big $(NPROCS) 2>&1 | tee rv32imfc_big_test.log

rv32imfdc_big_test:
	$(MAKE) rv32imfdc_big DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb scariv_tb_rv32imfdc_big rv32-tests.json log_rv32imfdc_big $(NPROCS) 2>&1 | tee rv32imfdc_big_test.log


#
# RV64
#
rv64imc_big: $(FILELIST) .config_design_xlen64_flen$(RV_FLEN)
#	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=big ISA=imc RV_XLEN=64 RV_FLEN=0 > $@_build.log 2>&1

rv64imfc_big: $(FILELIST) .config_design_xlen64_flen$(RV_FLEN)
#	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=big ISA=imfc RV_XLEN=64 RV_FLEN=32 > $@_build.log 2>&1

rv64imfdc_big: $(FILELIST) .config_design_xlen64_flen$(RV_FLEN)
#	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=big ISA=imfdc RV_XLEN=64 RV_FLEN=64 > $@_build.log 2>&1

rv64imc_big_test:
	$(MAKE) rv64imc_big DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb scariv_tb_rv64imc_big rv64-tests.json log_rv64imc_big $(NPROCS) 2>&1 | tee rv64imc_big_test.log

rv64imfc_big_test:
	$(MAKE) rv64imfc_big DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb scariv_tb_rv64imfc_big rv64-tests.json log_rv64imfc_big $(NPROCS) 2>&1 | tee rv64imfc_big_test.log

rv64imfdc_big_test:
	$(MAKE) rv64imfdc_big DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb scariv_tb_rv64imfdc_big rv64-tests.json log_rv64imfdc_big $(NPROCS) 2>&1 | tee rv64imfdc_big_test.log

rv64imc_big_benchmarks:
	$(MAKE) rv64imc_big DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb scariv_tb_rv64imc_big rv64-bench.json log_rv64imc_big $(NPROCS) 2>&1 | tee rv64imc_big_benchmark.log

rv64imfc_big_benchmarks:
	$(MAKE) rv64imfc_big DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb scariv_tb_rv64imfc_big rv64-bench.json log_rv64imfc_big $(NPROCS) 2>&1 | tee rv64imfc_big_benchmark.log

rv64imfdc_big_benchmarks:
	$(MAKE) rv64imfdc_big DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb scariv_tb_rv64imfdc_big rv64-bench.json log_rv64imfdc_big $(NPROCS) 2>&1 | tee rv64imfdc_big_benchmark.log

rv64imc_big_aapg:
	$(MAKE) rv64imc_big DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb scariv_tb_rv64imc_big     ../tests/aapg.json log_rv64imc_big_aapg  	  $(NPROCS) 2>&1 | tee rv64imc_big_aapg.log

rv64imfc_big_aapg:
	$(MAKE) rv64imfc_big DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb scariv_tb_rv64imfc_big     ../tests/aapg.json log_rv64imfc_big_aapg  	  $(NPROCS) 2>&1 | tee rv64imfc_big_aapg.log

rv64imfdc_big_aapg:
	$(MAKE) rv64imfdc_big DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb scariv_tb_rv64imfdc_big     ../tests/aapg.json log_rv64imfdc_big_aapg	  $(NPROCS) 2>&1 | tee rv64imfdc_big_aapg.log
