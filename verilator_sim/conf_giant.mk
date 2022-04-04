REGRESSION_LIST += rv32imc_giant_test
REGRESSION_LIST += rv32imfc_giant_test
REGRESSION_LIST += rv32imfdc_giant_test
REGRESSION_LIST += rv64imc_giant_test
REGRESSION_LIST += rv64imfc_giant_test
REGRESSION_LIST += rv64imfdc_giant_test
REGRESSION_LIST += rv64imc_giant_benchmarks
REGRESSION_LIST += rv64imfc_giant_benchmarks
REGRESSION_LIST += rv64imfdc_giant_benchmarks
REGRESSION_LIST += rv64imc_giant_aapg
REGRESSION_LIST += rv64imfc_giant_aapg
REGRESSION_LIST += rv64imfdc_giant_aapg

#
# RV32
#
rv32imc_giant: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=giant ISA=imc

rv32imfc_giant: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=giant ISA=imfc

rv32imfdc_giant: $(FILELIST) .config_design_rv32
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv32_build CONF=giant ISA=imfdc

rv32imc_giant_test:
	$(MAKE) rv32imc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imc_giant rv32-tests.json log_rv32imc_giant $(NPROCS) 2>&1 | tee rv32imc_giant_test.log

rv32imfc_giant_test:
	$(MAKE) rv32imfc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imfc_giant rv32-tests.json log_rv32imfc_giant $(NPROCS) 2>&1 | tee rv32imfc_giant_test.log

rv32imfdc_giant_test:
	$(MAKE) rv32imfdc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv32imfdc_giant rv32-tests.json log_rv32imfdc_giant $(NPROCS) 2>&1 | tee rv32imfdc_giant_test.log


#
# RV64
#
rv64imc_giant: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=giant ISA=imc

rv64imfc_giant: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=giant ISA=imfc

rv64imfdc_giant: $(FILELIST) .config_design_rv64
	$(MAKE) -C ../spike_dpi libspike_dpi.so VERILATOR=1
	$(MAKE) rv64_build CONF=giant ISA=imfdc

rv64imc_giant_test:
	$(MAKE) rv64imc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_giant rv64-tests.json log_rv64imc_giant $(NPROCS) 2>&1 | tee rv64imc_giant_test.log

rv64imfc_giant_test:
	$(MAKE) rv64imfc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_giant rv64-tests.json log_rv64imfc_giant $(NPROCS) 2>&1 | tee rv64imfc_giant_test.log

rv64imfdc_giant_test:
	$(MAKE) rv64imfdc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_giant rv64-tests.json log_rv64imfdc_giant $(NPROCS) 2>&1 | tee rv64imfdc_giant_test.log

rv64imc_giant_benchmarks:
	$(MAKE) rv64imc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_giant rv64-bench.json log_rv64imc_giant $(NPROCS) 2>&1 | tee rv64imc_giant_benchmark.log

rv64imfc_giant_benchmarks:
	$(MAKE) rv64imfc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_giant rv64-bench.json log_rv64imfc_giant $(NPROCS) 2>&1 | tee rv64imfc_giant_benchmark.log

rv64imfdc_giant_benchmarks:
	$(MAKE) rv64imfdc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_giant rv64-bench.json log_rv64imfdc_giant $(NPROCS) 2>&1 | tee rv64imfdc_giant_benchmark.log

rv64imc_giant_aapg:
	$(MAKE) rv64imc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imc_giant     ../tests/aapg.json log_rv64imc_giant_aapg  	  $(NPROCS) 2>&1 | tee rv64imc_giant_aapg.log

rv64imfc_giant_aapg:
	$(MAKE) rv64imfc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfc_giant     ../tests/aapg.json log_rv64imfc_giant_aapg  	  $(NPROCS) 2>&1 | tee rv64imfc_giant_aapg.log

rv64imfdc_giant_aapg:
	$(MAKE) rv64imfdc_giant DEBUG=off
	../scripts/runtest.rb msrh_tb_rv64imfdc_giant     ../tests/aapg.json log_rv64imfdc_giant_aapg	  $(NPROCS) 2>&1 | tee rv64imfdc_giant_aapg.log
