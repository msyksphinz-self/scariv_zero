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
rv32imc_tiny: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imc

rv32imfc_tiny: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imfc

rv32imfdc_tiny: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=tiny ISA=imfdc

rv32imc_tiny_test:
	$(MAKE) rv32imc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imc_tiny rv32-tests.json log_rv32imc_tiny $(NPROCS) 2>&1 | tee rv32imc_tiny_test.log

rv32imfc_tiny_test:
	$(MAKE) rv32imfc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imfc_tiny rv32-tests.json log_rv32imfc_tiny $(NPROCS) 2>&1 | tee rv32imfc_tiny_test.log

rv32imfdc_tiny_test:
	$(MAKE) rv32imfdc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imfdc_tiny rv32-tests.json log_rv32imfdc_tiny $(NPROCS) 2>&1 | tee rv32imfdc_tiny_test.log


#
# RV64
#
rv64imc_tiny: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=tiny ISA=imc

rv64imfc_tiny: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=tiny ISA=imfc

rv64imfdc_tiny: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=tiny ISA=imfdc

rv64imc_tiny_test:
	$(MAKE) rv64imc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_tiny rv64-tests.json log_rv64imc_tiny $(NPROCS) 2>&1 | tee rv64imc_tiny_test.log

rv64imfc_tiny_test:
	$(MAKE) rv64imfc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_tiny rv64-tests.json log_rv64imfc_tiny $(NPROCS) 2>&1 | tee rv64imfc_tiny_test.log

rv64imfdc_tiny_test:
	$(MAKE) rv64imfdc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_tiny rv64-tests.json log_rv64imfdc_tiny $(NPROCS) 2>&1 | tee rv64imfdc_tiny_test.log

rv64imc_tiny_benchmarks:
	$(MAKE) rv64imc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_tiny rv64-bench.json log_rv64imc_tiny $(NPROCS) 2>&1 | tee rv64imc_tiny_benchmark.log

rv64imfc_tiny_benchmarks:
	$(MAKE) rv64imfc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_tiny rv64-bench.json log_rv64imfc_tiny $(NPROCS) 2>&1 | tee rv64imfc_tiny_benchmark.log

rv64imfdc_tiny_benchmarks:
	$(MAKE) rv64imfdc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_tiny rv64-bench.json log_rv64imfdc_tiny $(NPROCS) 2>&1 | tee rv64imfdc_tiny_benchmark.log

rv64imc_tiny_aapg:
	$(MAKE) rv64imc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_tiny     ../tests/aapg.json log_rv64imc_tiny_aapg  	  $(NPROCS) 2>&1 | tee rv64imc_tiny_aapg.log

rv64imfc_tiny_aapg:
	$(MAKE) rv64imfc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_tiny     ../tests/aapg.json log_rv64imfc_tiny_aapg  	  $(NPROCS) 2>&1 | tee rv64imfc_tiny_aapg.log

rv64imfdc_tiny_aapg:
	$(MAKE) rv64imfdc_tiny DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_tiny     ../tests/aapg.json log_rv64imfdc_tiny_aapg	  $(NPROCS) 2>&1 | tee rv64imfdc_tiny_aapg.log
