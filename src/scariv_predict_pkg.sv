// ------------------------------------------------------------------------
// NAME : Packages for Branch Prediction
// TYPE : package
// ------------------------------------------------------------------------
// Packages used for branch prediction
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

package scariv_predict_pkg;

localparam BTB_ENTRY_SIZE = 1024;

localparam BTB_ENTRY_FIELD_MSB = $clog2(scariv_lsu_pkg::ICACHE_DATA_B_W/2);

localparam BTB_ENTRY_BIT_LSB   = BTB_ENTRY_FIELD_MSB + 1;
localparam BTB_ENTRY_BIT_MSB   = $clog2(BTB_ENTRY_SIZE) - 1 + BTB_ENTRY_BIT_LSB;

typedef logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] ras_idx_t;

typedef struct packed {
  logic valid;
  logic is_cond;
  logic is_call;
  logic is_ret;
  logic is_noncond;
  logic [riscv_pkg::VADDR_W-1:BTB_ENTRY_BIT_MSB+1] pc_tag;
} btb_inst_info_t;

typedef struct packed {
  scariv_pkg::vaddr_t target_vaddr;
} btb_target_va_t;

endpackage // scariv_predict_pkg

interface btb_search_if;

  logic                                                 s0_valid;
  scariv_pkg::vaddr_t                                     s0_pc_vaddr;
  scariv_ic_pkg::ic_block_t          s1_hit;
  scariv_ic_pkg::ic_block_vaddr_t    s1_target_vaddr;
  scariv_ic_pkg::ic_block_t          s1_is_cond;
  scariv_ic_pkg::ic_block_t          s1_is_call;
  scariv_ic_pkg::ic_block_t          s1_is_ret;
  scariv_ic_pkg::ic_block_t          s1_is_noncond;
  scariv_ic_pkg::ic_block_t          s2_hit;
  scariv_ic_pkg::ic_block_vaddr_t    s2_target_vaddr;
  scariv_ic_pkg::ic_block_t          s2_is_cond;
  scariv_ic_pkg::ic_block_t          s2_is_call;
  scariv_ic_pkg::ic_block_t          s2_is_ret;
  scariv_ic_pkg::ic_block_t          s2_is_noncond;

  modport master (
    output s0_valid,
    output s0_pc_vaddr,
    input  s1_hit,
    input  s1_target_vaddr,
    input  s1_is_cond,
    input  s1_is_call,
    input  s1_is_ret,
    input  s1_is_noncond,
    input  s2_hit,
    input  s2_target_vaddr,
    input  s2_is_cond,
    input  s2_is_call,
    input  s2_is_ret,
    input  s2_is_noncond
  );

  modport slave (
    input s0_valid,
    input s0_pc_vaddr,
    output s1_hit,
    output s1_target_vaddr,
    output s1_is_cond,
    output s1_is_call,
    output s1_is_ret,
    output s1_is_noncond,
    output s2_hit,
    output s2_target_vaddr,
    output s2_is_cond,
    output s2_is_call,
    output s2_is_ret,
    output s2_is_noncond
  );

  modport monitor (
    input s1_hit,
    input s1_is_cond,
    input s1_is_call,
    input s1_is_ret,
    input s1_is_noncond,
    input s1_target_vaddr,
    input s2_hit,
    input s2_target_vaddr,
    input s2_is_cond
  );

endinterface // btb_search_if


interface btb_update_if;

  logic              valid;
  logic              is_cond;
  logic              is_call;
  logic              is_ret;
  logic              is_rvc;
  logic              taken;
  logic              mispredict;
  scariv_pkg::vaddr_t  pc_vaddr;
  scariv_pkg::vaddr_t  target_vaddr;

  modport master (
    output valid,
    output is_cond,
    output is_call,
    output is_ret,
    output is_rvc,
    output taken,
    output mispredict,
    output pc_vaddr,
    output target_vaddr
  );

  modport slave (
    input valid,
    input is_cond,
    input is_call,
    input is_ret,
    input is_rvc,
    input taken,
    input mispredict,
    input pc_vaddr,
    input target_vaddr
  );

endinterface // btb_update_if


interface bim_search_if;

  logic                                                 s0_valid;
  scariv_pkg::vaddr_t                        s0_pc_vaddr;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][ 1: 0]   s1_bim_value;
  scariv_ic_pkg::ic_block_t          s1_pred_taken;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][ 1: 0]   s2_bim_value;
  scariv_ic_pkg::ic_block_t          s2_pred_taken;

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

  logic             valid;
  scariv_pkg::vaddr_t pc_vaddr;
  logic             hit;
  logic             taken;
  logic [ 1: 0]     bim_value;
  logic             is_rvc;

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

  scariv_ic_pkg::ic_block_t       s1_is_call;
  scariv_ic_pkg::ic_block_t       s1_is_ret;
  logic [riscv_pkg::VADDR_W-1: 1]                    s1_ras_vaddr;
  scariv_predict_pkg::ras_idx_t     s1_ras_index;

  scariv_ic_pkg::ic_block_t       s2_is_call;
  logic [riscv_pkg::VADDR_W-1: 1]                    s2_call_target_vaddr;
  scariv_ic_pkg::ic_block_t       s2_is_ret;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W-1: 0]         s2_ras_be;
  logic [riscv_pkg::VADDR_W-1: 1]                    s2_ras_vaddr;
  scariv_predict_pkg::ras_idx_t     s2_ras_index;

  modport master (
    output s1_is_call,
    output s1_is_ret,
    output s1_ras_vaddr,
    output s1_ras_index,
    output s2_is_call,
    output s2_call_target_vaddr,
    output s2_is_ret,
    output s2_ras_be,
    output s2_ras_vaddr,
    output s2_ras_index
  );

  modport slave (
    input s1_is_call,
    input s1_is_ret,
    input s1_ras_vaddr,
    input s1_ras_index,
    input s2_is_call,
    input s2_call_target_vaddr,
    input s2_is_ret,
    input s2_ras_be,
    input s2_ras_vaddr,
    input s2_ras_index
  );

endinterface // bim_search_if


interface gshare_search_if;

  logic                  s0_valid;
  scariv_pkg::vaddr_t      s0_pc_vaddr;

  logic                                                                     s2_valid;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]                              s2_pred_taken;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][ 1: 0]                       s2_bim_value;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][scariv_pkg::GSHARE_BHT_W-1: 0] s2_index;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][scariv_pkg::GSHARE_BHT_W-1: 0] s2_bhr;

  modport master (
    output s0_valid,
    output s0_pc_vaddr,
    input  s2_valid,
    input  s2_pred_taken,
    input  s2_bim_value,
    input  s2_index,
    input  s2_bhr
  );

  modport slave (
    input  s0_valid,
    input  s0_pc_vaddr,
    output s2_valid,
    output s2_pred_taken,
    output s2_bim_value,
    output s2_index,
    output s2_bhr
  );

  modport monitor (
    input s2_valid,
    input s2_index,
    input s2_pred_taken,
    input s2_bim_value,
    input s2_bhr
  );


endinterface // gshare_search_if
