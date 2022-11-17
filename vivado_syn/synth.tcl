set PROJ_NAME msrh_tile_wrapper
set PROJ_DIR .
set RTL_ROOT_DIR ../src
set TOP_NAME msrh_tile_wrapper

create_project -in_memory -part xc7z020clg484-1 $PROJ_NAME $PROJ_DIR
save_project_as -force $PROJ_NAME $PROJ_DIR/$PROJ_NAME.xpr

set_property parent.project_path ${PROJ_DIR}/${PROJ_NAME}.xpr [current_project]
set_property default_lib xil_defaultlib [current_project]
set_property target_language Verilog [current_project]
set_property board_part em.avnet.com:zed:part0:1.3 [current_project]
set_property vhdl_version vhdl_2k [current_fileset]

add_files -norecurse ../src/riscv_common_pkg.sv
import_files ../src/riscv_common_pkg.sv
add_files -norecurse ../src/riscv_fpu_imafdc_pkg.sv
import_files ../src/riscv_fpu_imafdc_pkg.sv
add_files -norecurse ../src/riscv64_pkg.sv
import_files ../src/riscv64_pkg.sv
add_files -norecurse ../src/msrh_standard_conf_pkg.sv
import_files ../src/msrh_standard_conf_pkg.sv

# add_files -norecurse $RTL_ROOT_DIR
source filelist.tcl
import_files

add_files -norecurse ../src/msrh_tile_wrapper.sv
import_files ../src/msrh_tile_wrapper.sv

read_xdc synth_constraints.xdc
set_property used_in_implementation false [get_files synth_constraints.xdc]

# read_xdc dont_touch.xdc
# set_property used_in_implementation false [get_files dont_touch.xdc]

synth_design -top ${TOP_NAME} -part xc7z020clg484-1 -fanout_limit 10000 \
    -flatten_hierarchy rebuilt \
    -include_dir ../src/fpnew/src/common_cells/include \
    -include_dir ../src \
    -verilog_define RV64
write_checkpoint -force ${TOP_NAME}.dcp
report_utilization -file ${TOP_NAME}_utilization_synth.rpt -pb ${TOP_NAME}_utilization_synth.pb
report_timing -file ${TOP_NAME}_timing_synth.rpt

exit
