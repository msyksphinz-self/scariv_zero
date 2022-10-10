REGRESSION_LIST += rv32imc_tiny_test
REGRESSION_LIST += rv32imfc_tiny_test
REGRESSION_LIST += rv32imfdc_tiny_test
REGRESSION_LIST += rv64imc_tiny_test
REGRESSION_LIST += rv64imfc_tiny_test
REGRESSION_LIST += rv64imfdc_tiny_test
REGRESSION_LIST += rv64imc_tiny_benchmarks
REGRESSION_LIST += rv64imfc_tiny_benchmarks
REGRESSION_LIST += rv64imfdc_tiny_benchmarks
REGRESSION_LIST += rv64imc_tiny_aapg
REGRESSION_LIST += rv64imfc_tiny_aapg
REGRESSION_LIST += rv64imfdc_tiny_aapg

#
# RV32
#
rv32imc_tiny: $(FILELIST) .config_design_xlen32_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imc RV_XLEN=32 RV_FLEN=0 RV_AMO=0 > $@_build.log 2>&1

rv32imfc_tiny: $(FILELIST) .config_design_xlen32_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imfc RV_XLEN=32 RV_FLEN=32 RV_AMO=0 > $@_build.log 2>&1

rv32imfdc_tiny: $(FILELIST) .config_design_xlen32_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imfdc RV_XLEN=32 RV_FLEN=64 RV_AMO=0 > $@_build.log 2>&1

rv32imc_tiny_test:
	$(MAKE) rv32imc_tiny DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb msrh_tb_rv32imc_tiny rv32-tests.json log_rv32imc_tiny $(NPROCS) 2>&1 | tee rv32imc_tiny_test.log

rv32imfc_tiny_test:
	$(MAKE) rv32imfc_tiny DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb msrh_tb_rv32imfc_tiny rv32-tests.json log_rv32imfc_tiny $(NPROCS) 2>&1 | tee rv32imfc_tiny_test.log

rv32imfdc_tiny_test:
	$(MAKE) rv32imfdc_tiny DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb msrh_tb_rv32imfdc_tiny rv32-tests.json log_rv32imfdc_tiny $(NPROCS) 2>&1 | tee rv32imfdc_tiny_test.log

rv32imac_tiny: $(FILELIST) .config_design_xlen32_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imac RV_XLEN=32 RV_FLEN=0 RV_AMO=1 > $@_build.log 2>&1

rv32imafc_tiny: $(FILELIST) .config_design_xlen32_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imafc RV_XLEN=32 RV_FLEN=32 RV_AMO=1 > $@_build.log 2>&1

rv32imafdc_tiny: $(FILELIST) .config_design_xlen32_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imafdc RV_XLEN=32 RV_FLEN=64 RV_AMO=1 > $@_build.log 2>&1

rv32imac_tiny_test:
	$(MAKE) rv32imac_tiny DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb msrh_tb_rv32imac_tiny rv32-tests.json log_rv32imac_tiny $(NPROCS) 2>&1 | tee rv32imac_tiny_test.log

rv32imafc_tiny_test:
	$(MAKE) rv32imafc_tiny DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb msrh_tb_rv32imafc_tiny rv32-tests.json log_rv32imafc_tiny $(NPROCS) 2>&1 | tee rv32imafc_tiny_test.log

rv32imafdc_tiny_test:
	$(MAKE) rv32imafdc_tiny DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb msrh_tb_rv32imafdc_tiny rv32-tests.json log_rv32imafdc_tiny $(NPROCS) 2>&1 | tee rv32imafdc_tiny_test.log

#
# RV64
#
rv64imc_tiny: $(FILELIST) .config_design_xlen64_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=tiny ISA=imc RV_XLEN=64 RV_FLEN=0 RV_AMO=0 > $@_build.log 2>&1

rv64imfc_tiny: $(FILELIST) .config_design_xlen64_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=tiny ISA=imfc RV_XLEN=64 RV_FLEN=32 RV_AMO=0 > $@_build.log 2>&1

rv64imfdc_tiny: $(FILELIST) .config_design_xlen64_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi all VERILATOR=1
	$(MAKE) rv64_build CONF=tiny ISA=imfdc RV_XLEN=64 RV_FLEN=64 RV_AMO=0 > $@_build.log 2>&1

rv64imc_tiny_test:
	$(MAKE) rv64imc_tiny DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb msrh_tb_rv64imc_tiny rv64-tests.json log_rv64imc_tiny $(NPROCS) 2>&1 | tee rv64imc_tiny_test.log

rv64imfc_tiny_test:
	$(MAKE) rv64imfc_tiny DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb msrh_tb_rv64imfc_tiny rv64-tests.json log_rv64imfc_tiny $(NPROCS) 2>&1 | tee rv64imfc_tiny_test.log

rv64imfdc_tiny_test:
	$(MAKE) rv64imfdc_tiny DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb msrh_tb_rv64imfdc_tiny rv64-tests.json log_rv64imfdc_tiny $(NPROCS) 2>&1 | tee rv64imfdc_tiny_test.log

rv64imc_tiny_benchmarks:
	$(MAKE) rv64imc_tiny DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb msrh_tb_rv64imc_tiny rv64-bench.json log_rv64imc_tiny $(NPROCS) 2>&1 | tee rv64imc_tiny_benchmark.log

rv64imfc_tiny_benchmarks:
	$(MAKE) rv64imfc_tiny DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb msrh_tb_rv64imfc_tiny rv64-bench.json log_rv64imfc_tiny $(NPROCS) 2>&1 | tee rv64imfc_tiny_benchmark.log

rv64imfdc_tiny_benchmarks:
	$(MAKE) rv64imfdc_tiny DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb msrh_tb_rv64imfdc_tiny rv64-bench.json log_rv64imfdc_tiny $(NPROCS) 2>&1 | tee rv64imfdc_tiny_benchmark.log

rv64imc_tiny_aapg:
	$(MAKE) rv64imc_tiny DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb msrh_tb_rv64imc_tiny     ../tests/aapg.json log_rv64imc_tiny_aapg  	  $(NPROCS) 2>&1 | tee rv64imc_tiny_aapg.log

rv64imfc_tiny_aapg:
	$(MAKE) rv64imfc_tiny DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb msrh_tb_rv64imfc_tiny     ../tests/aapg.json log_rv64imfc_tiny_aapg  	  $(NPROCS) 2>&1 | tee rv64imfc_tiny_aapg.log

rv64imfdc_tiny_aapg:
	$(MAKE) rv64imfdc_tiny DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb msrh_tb_rv64imfdc_tiny     ../tests/aapg.json log_rv64imfdc_tiny_aapg	  $(NPROCS) 2>&1 | tee rv64imfdc_tiny_aapg.log

rv64imac_tiny: $(FILELIST) .config_design_xlen64_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=tiny ISA=imac RV_XLEN=64 RV_FLEN=0 RV_AMO=1 > $@_build.log 2>&1

rv64imafc_tiny: $(FILELIST) .config_design_xlen64_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=tiny ISA=imafc RV_XLEN=64 RV_FLEN=32 RV_AMO=1 > $@_build.log 2>&1

rv64imafdc_tiny: $(FILELIST) .config_design_xlen64_flen$(RV_FLEN) .tests_build_done
	$(MAKE) -C ../spike_dpi all VERILATOR=1
	$(MAKE) rv64_build CONF=tiny ISA=imafdc RV_XLEN=64 RV_FLEN=64 RV_AMO=1 > $@_build.log 2>&1

rv64imac_tiny_test:
	$(MAKE) rv64imac_tiny DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb msrh_tb_rv64imac_tiny rv64-tests.json log_rv64imac_tiny $(NPROCS) 2>&1 | tee rv64imac_tiny_test.log

rv64imafc_tiny_test:
	$(MAKE) rv64imafc_tiny DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb msrh_tb_rv64imafc_tiny rv64-tests.json log_rv64imafc_tiny $(NPROCS) 2>&1 | tee rv64imafc_tiny_test.log

rv64imafdc_tiny_test:
	$(MAKE) rv64imafdc_tiny DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb msrh_tb_rv64imafdc_tiny rv64-tests.json log_rv64imafdc_tiny $(NPROCS) 2>&1 | tee rv64imafdc_tiny_test.log

rv64imac_tiny_benchmarks:
	$(MAKE) rv64imac_tiny DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb msrh_tb_rv64imac_tiny rv64-bench.json log_rv64imac_tiny $(NPROCS) 2>&1 | tee rv64imac_tiny_benchmark.log

rv64imafc_tiny_benchmarks:
	$(MAKE) rv64imafc_tiny DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb msrh_tb_rv64imafc_tiny rv64-bench.json log_rv64imafc_tiny $(NPROCS) 2>&1 | tee rv64imafc_tiny_benchmark.log

rv64imafdc_tiny_benchmarks:
	$(MAKE) rv64imafdc_tiny DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb msrh_tb_rv64imafdc_tiny rv64-bench.json log_rv64imafdc_tiny $(NPROCS) 2>&1 | tee rv64imafdc_tiny_benchmark.log

rv64imac_tiny_aapg:
	$(MAKE) rv64imac_tiny DEBUG=off RV_FLEN=0
	../scripts/run_regress.rb msrh_tb_rv64imac_tiny     ../tests/aapg.json log_rv64imac_tiny_aapg  	  $(NPROCS) 2>&1 | tee rv64imac_tiny_aapg.log

rv64imafc_tiny_aapg:
	$(MAKE) rv64imafc_tiny DEBUG=off RV_FLEN=32
	../scripts/run_regress.rb msrh_tb_rv64imafc_tiny     ../tests/aapg.json log_rv64imafc_tiny_aapg  	  $(NPROCS) 2>&1 | tee rv64imafc_tiny_aapg.log

rv64imafdc_tiny_aapg:
	$(MAKE) rv64imafdc_tiny DEBUG=off RV_FLEN=64
	../scripts/run_regress.rb msrh_tb_rv64imafdc_tiny     ../tests/aapg.json log_rv64imafdc_tiny_aapg	  $(NPROCS) 2>&1 | tee rv64imafdc_tiny_aapg.log
