REGRESSION_LIST += rv32imc_standard_test
REGRESSION_LIST += rv32imfc_standard_test
REGRESSION_LIST += rv32imfdc_standard_test
REGRESSION_LIST += rv64imc_standard_test
REGRESSION_LIST += rv64imfc_standard_test
REGRESSION_LIST += rv64imfdc_standard_test
REGRESSION_LIST += rv64imc_standard_benchmarks
REGRESSION_LIST += rv64imfc_standard_benchmarks
REGRESSION_LIST += rv64imfdc_standard_benchmarks
REGRESSION_LIST += rv64imc_standard_aapg
REGRESSION_LIST += rv64imfc_standard_aapg
REGRESSION_LIST += rv64imfdc_standard_aapg

#
# RV32
#
rv32imc_standard: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=standard ISA=imc

rv32imfc_standard: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=standard ISA=imfc

rv32imfdc_standard: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=standard ISA=imfdc

rv32imc_standard_test:
	$(MAKE) rv32imc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imc_standard rv32-tests.json log_rv32imc_standard $(NPROCS) 2>&1 | tee rv32imc_standard_test.log

rv32imfc_standard_test:
	$(MAKE) rv32imfc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imfc_standard rv32-tests.json log_rv32imfc_standard $(NPROCS) 2>&1 | tee rv32imfc_standard_test.log

rv32imfdc_standard_test:
	$(MAKE) rv32imfdc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imfdc_standard rv32-tests.json log_rv32imfdc_standard $(NPROCS) 2>&1 | tee rv32imfdc_standard_test.log


#
# RV64
#
rv64imc_standard: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=standard ISA=imc

rv64imfc_standard: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=standard ISA=imfc

rv64imfdc_standard: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=standard ISA=imfdc

rv64imc_standard_test:
	$(MAKE) rv64imc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_standard rv64-tests.json log_rv64imc_standard $(NPROCS) 2>&1 | tee rv64imc_standard_test.log

rv64imfc_standard_test:
	$(MAKE) rv64imfc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_standard rv64-tests.json log_rv64imfc_standard $(NPROCS) 2>&1 | tee rv64imfc_standard_test.log

rv64imfdc_standard_test:
	$(MAKE) rv64imfdc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_standard rv64-tests.json log_rv64imfdc_standard $(NPROCS) 2>&1 | tee rv64imfdc_standard_test.log

rv64imc_standard_benchmarks:
	$(MAKE) rv64imc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_standard rv64-bench.json log_rv64imc_standard $(NPROCS) 2>&1 | tee rv64imc_standard_benchmark.log

rv64imfc_standard_benchmarks:
	$(MAKE) rv64imfc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_standard rv64-bench.json log_rv64imfc_standard $(NPROCS) 2>&1 | tee rv64imfc_standard_benchmark.log

rv64imfdc_standard_benchmarks:
	$(MAKE) rv64imfdc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_standard rv64-bench.json log_rv64imfdc_standard $(NPROCS) 2>&1 | tee rv64imfdc_standard_benchmark.log

rv64imc_standard_aapg:
	$(MAKE) rv64imc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_standard     ../tests/aapg.json log_rv64imc_standard_aapg  	  $(NPROCS) 2>&1 | tee rv64imc_standard_aapg.log

rv64imfc_standard_aapg:
	$(MAKE) rv64imfc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_standard     ../tests/aapg.json log_rv64imfc_standard_aapg  	  $(NPROCS) 2>&1 | tee rv64imfc_standard_aapg.log

rv64imfdc_standard_aapg:
	$(MAKE) rv64imfdc_standard DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_standard     ../tests/aapg.json log_rv64imfdc_standard_aapg	  $(NPROCS) 2>&1 | tee rv64imfdc_standard_aapg.log
