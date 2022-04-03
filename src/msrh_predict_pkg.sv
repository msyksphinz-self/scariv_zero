// ------------------------------------------------------------------------
// NAME : Packages for Branch Prediction
// TYPE : package
// ------------------------------------------------------------------------
// Packages used for branch prediction
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

package msrh_predict_pkg;

localparam BTB_ENTRY_SIZE = 1024;

localparam BTB_ENTRY_FIELD_MSB = $clog2(msrh_lsu_pkg::ICACHE_DATA_B_W/2);

localparam BTB_ENTRY_BIT_LSB   = BTB_ENTRY_FIELD_MSB + 1;
localparam BTB_ENTRY_BIT_MSB   = $clog2(BTB_ENTRY_SIZE) - 1 + BTB_ENTRY_BIT_LSB;

typedef struct packed {
  logic                                            valid;
  logic                                            is_call;
  logic                                            is_ret;
  logic [riscv_pkg::VADDR_W-1:BTB_ENTRY_BIT_MSB+1] pc_tag;
  msrh_pkg::vaddr_t                   target_vaddr;
} btb_entry_t;

endpackage // msrh_predict_pkg

interface btb_search_if;

  logic                                                 s0_valid;
  msrh_pkg::vaddr_t                        s0_pc_vaddr;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]          s1_hit;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][riscv_pkg::VADDR_W-1:0] s1_target_vaddr;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]          s1_is_call;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]          s1_is_ret;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]          s2_hit;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][riscv_pkg::VADDR_W-1:0] s2_target_vaddr;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]          s2_is_call;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]          s2_is_ret;

  modport master (
    output s0_valid,
    output s0_pc_vaddr,
    input  s1_hit,
    input  s1_target_vaddr,
    input  s1_is_call,
    input  s1_is_ret,
    input  s2_hit,
    input  s2_target_vaddr,
    input  s2_is_call,
    input  s2_is_ret
  );

  modport slave (
    input s0_valid,
    input s0_pc_vaddr,
    output s1_hit,
    output s1_target_vaddr,
    output s1_is_call,
    output s1_is_ret,
    output s2_hit,
    output s2_target_vaddr,
    output s2_is_call,
    output s2_is_ret
  );

  modport monitor (
    input s1_hit,
    input s1_target_vaddr,
    input s2_hit,
    input s2_target_vaddr
  );

endinterface // btb_search_if


interface btb_update_if;

  logic                                                 valid;
  logic                                                 is_call;
  logic                                                 is_ret;
  logic                                                 is_rvc;
  msrh_pkg::vaddr_t                        pc_vaddr;
  msrh_pkg::vaddr_t                        target_vaddr;

  modport master (
    output valid,
    output is_call,
    output is_ret,
    output is_rvc,
    output pc_vaddr,
    output target_vaddr
  );

  modport slave (
    input valid,
    input is_call,
    input is_ret,
    input is_rvc,
    input pc_vaddr,
    input target_vaddr
  );

endinterface // btb_update_if


interface bim_search_if;

  logic                                                 s0_valid;
  msrh_pkg::vaddr_t                        s0_pc_vaddr;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][ 1: 0]   s1_bim_value;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]          s1_pred_taken;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][ 1: 0]   s2_bim_value;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]          s2_pred_taken;

  modport master (
    output s0_valid,
    output s0_pc_vaddr,
    input  s1_bim_value,
    input  s1_pred_taken,
    input  s2_bim_value,
    input  s2_pred_taken
  );

  modport slave (
    input s0_valid,
    input s0_pc_vaddr,
    output s1_bim_value,
    output s1_pred_taken,
    output s2_bim_value,
    output s2_pred_taken
  );

  modport monitor (
    input s1_bim_value,
    input s2_bim_value
  );

endinterface // bim_search_if


interface bim_update_if;

  logic                                                 valid;
  msrh_pkg::vaddr_t                        pc_vaddr;
  logic                                                 hit;
  logic                                                 taken;
  logic [ 1: 0]                                         bim_value;
  logic                                                 is_rvc;

  modport master (
    output valid,
    output pc_vaddr,
    output hit,
    output taken,
    output bim_value,
    output is_rvc
  );

  modport slave (
    input valid,
    input pc_vaddr,
    input hit,
    input taken,
    input bim_value,
    input is_rvc
  );

endinterface // bim_update_if


interface ras_search_if;

  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]       s1_is_call;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]       s1_is_ret;
  logic [riscv_pkg::VADDR_W-1: 1]                    s1_ras_vaddr;
  logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] s1_ras_index;

  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]       s2_is_call;
  logic [msrh_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]       s2_is_ret;
  logic [riscv_pkg::VADDR_W-1: 1]                    s2_ras_vaddr;
  logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] s2_ras_index;

  modport master (
    output s1_is_call,
    output s1_is_ret,
    output s1_ras_vaddr,
    output s1_ras_index,
    output s2_is_call,
    output s2_is_ret,
    output s2_ras_vaddr,
    output s2_ras_index
  );

  modport slave (
    input s1_is_call,
    input s1_is_ret,
    input s1_ras_vaddr,
    input s1_ras_index,
    input s2_is_call,
    input s2_is_ret,
    input s2_ras_vaddr,
    input s2_ras_index
  );

endinterface // bim_search_if
