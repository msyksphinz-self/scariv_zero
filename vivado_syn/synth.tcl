set PROJ_NAME scariv_tile_wrapper
set PROJ_DIR .
set RTL_ROOT_DIR ../../src
set TOP_NAME scariv_tile_wrapper

# set DEVICE_NAME xc7z045ffg900
set DEVICE_NAME xc7z030fbg484

create_project -in_memory -part $DEVICE_NAME $PROJ_NAME $PROJ_DIR
save_project_as -force $PROJ_NAME $PROJ_DIR/$PROJ_NAME.xpr

set_property parent.project_path ${PROJ_DIR}/${PROJ_NAME}.xpr [current_project]
set_property default_lib xil_defaultlib [current_project]
set_property target_language Verilog [current_project]
set_property board_part em.avnet.com:zed:part0:1.3 [current_project]
set_property vhdl_version vhdl_2k [current_fileset]

add_files -norecurse ../../src/riscv_common_pkg.sv
import_files ../../src/riscv_common_pkg.sv

add_files -norecurse ../../src/$::env(FPU_FILE)
import_files ../../src/$::env(FPU_FILE)

add_files -norecurse ../../src/$::env(RV_FILE)
import_files ../../src/$::env(RV_FILE)

add_files -norecurse ../../src/$::env(CONF_FILE)
import_files ../../src/$::env(CONF_FILE)

# add_files -norecurse $RTL_ROOT_DIR
source filelist.tcl
import_files

read_xdc ../synth_constraints.xdc
# set_property used_in_implementation false [get_files ../synth_constraints.xdc]

# read_xdc dont_touch.xdc
# set_property used_in_implementation false [get_files dont_touch.xdc]

synth_design -top ${TOP_NAME} -part $DEVICE_NAME -fanout_limit 10000 \
    -flatten_hierarchy rebuilt \
    -include_dir ../../src/fpnew/src/common_cells/include \
    -include_dir ../../src \
    -verilog_define $::env(RV_DEFINE)
write_checkpoint -force ${TOP_NAME}.dcp
report_utilization -file ${TOP_NAME}_utilization_synth.rpt -pb ${TOP_NAME}_utilization_synth.pb
report_utilization -file ${TOP_NAME}.area.hier1.rpt -hierarchical -hierarchical_depth 1
report_utilization -file ${TOP_NAME}.area.hier2.rpt -hierarchical -hierarchical_depth 2
report_utilization -file ${TOP_NAME}.area.hier3.rpt -hierarchical -hierarchical_depth 3
report_utilization -file ${TOP_NAME}.area.hier.rpt  -hierarchical

report_timing -file ${TOP_NAME}_timing_synth.rpt

exit
