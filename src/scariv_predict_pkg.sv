// ------------------------------------------------------------------------
// NAME : Packages for Branch Prediction
// TYPE : package
// ------------------------------------------------------------------------
// Packages used for branch prediction
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

package scariv_predict_pkg;

localparam BTB_ENTRY_FIELD_MSB = $clog2(scariv_lsu_pkg::ICACHE_DATA_B_W/2);

localparam BTB_ENTRY_BIT_LSB   = BTB_ENTRY_FIELD_MSB + 1;
localparam BTB_ENTRY_BIT_MSB   = $clog2(scariv_conf_pkg::BTB_ENTRY_SIZE) - 1 + BTB_ENTRY_BIT_LSB;

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

typedef struct packed {
  logic [$clog2(scariv_conf_pkg::ICACHE_DATA_W/8)-1: 0] pc_offset;
  logic                                                 taken;
  scariv_pkg::vaddr_t                                   target_vaddr;
} ubtb_info_t;

function automatic logic [scariv_conf_pkg::GSHARE_BHT_W-1: 0] fold_hash_index (input logic [scariv_conf_pkg::GSHARE_HIST_LEN-1: 0] in);
  integer chunks = (scariv_conf_pkg::GSHARE_HIST_LEN + scariv_conf_pkg::GSHARE_BHT_W - 1) / scariv_conf_pkg::GSHARE_BHT_W;
  logic [scariv_conf_pkg::GSHARE_BHT_W-1: 0] ret;
  ret = 0;
  for (int i = 0; i < chunks; i++) begin
    ret = ret ^ in[i* scariv_conf_pkg::GSHARE_BHT_W +: scariv_conf_pkg::GSHARE_BHT_W];
  end
  return ret;
endfunction // fold_hash_index

endpackage // scariv_predict_pkg

interface btb_search_if;

  logic                              f0_valid;
  scariv_pkg::vaddr_t                f0_pc_vaddr;
  scariv_ic_pkg::ic_block_t          f1_hit;
  scariv_ic_pkg::ic_block_t          f1_pc_vaddr_mask;
  scariv_ic_pkg::ic_block_vaddr_t    f1_target_vaddr;
  scariv_ic_pkg::ic_block_t          f1_is_cond;
  scariv_ic_pkg::ic_block_t          f1_is_call;
  scariv_ic_pkg::ic_block_t          f1_is_ret;
  scariv_ic_pkg::ic_block_t          f1_is_noncond;
  scariv_ic_pkg::ic_block_t          f2_hit;
  scariv_ic_pkg::ic_block_vaddr_t    f2_target_vaddr;
  scariv_ic_pkg::ic_block_t          f2_is_cond;
  scariv_ic_pkg::ic_block_t          f2_is_call;
  scariv_ic_pkg::ic_block_t          f2_is_ret;
  scariv_ic_pkg::ic_block_t          f2_is_noncond;

  modport master (
    output f0_valid,
    output f0_pc_vaddr,
    input  f1_hit,
    input  f1_pc_vaddr_mask,
    input  f1_target_vaddr,
    input  f1_is_cond,
    input  f1_is_call,
    input  f1_is_ret,
    input  f1_is_noncond,
    input  f2_hit,
    input  f2_target_vaddr,
    input  f2_is_cond,
    input  f2_is_call,
    input  f2_is_ret,
    input  f2_is_noncond
  );

  modport slave (
    input f0_valid,
    input f0_pc_vaddr,
    output f1_hit,
    output f1_pc_vaddr_mask,
    output f1_target_vaddr,
    output f1_is_cond,
    output f1_is_call,
    output f1_is_ret,
    output f1_is_noncond,
    output f2_hit,
    output f2_target_vaddr,
    output f2_is_cond,
    output f2_is_call,
    output f2_is_ret,
    output f2_is_noncond
  );

  modport monitor (
    input f1_hit,
    input f1_is_cond,
    input f1_is_call,
    input f1_is_ret,
    input f1_is_noncond,
    input f1_target_vaddr,
    input f2_hit,
    input f2_target_vaddr,
    input f2_is_cond
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

  logic                                                 f0_valid;
  scariv_pkg::vaddr_t                        f0_pc_vaddr;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][ 1: 0]   f1_bim_value;
  scariv_ic_pkg::ic_block_t          f1_pred_taken;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][ 1: 0]   f2_bim_value;
  scariv_ic_pkg::ic_block_t          f2_pred_taken;

  modport master (
    output f0_valid,
    output f0_pc_vaddr,
    input  f1_bim_value,
    input  f1_pred_taken,
    input  f2_bim_value,
    input  f2_pred_taken
  );

  modport slave (
    input f0_valid,
    input f0_pc_vaddr,
    output f1_bim_value,
    output f1_pred_taken,
    output f2_bim_value,
    output f2_pred_taken
  );

  modport monitor (
    input f1_bim_value,
    input f2_bim_value
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

  scariv_ic_pkg::ic_block_t       f1_is_call;
  scariv_ic_pkg::ic_block_t       f1_is_ret;
  logic [riscv_pkg::VADDR_W-1: 1]                    f1_ras_vaddr;
  scariv_predict_pkg::ras_idx_t     f1_ras_index;

  scariv_ic_pkg::ic_block_t       f2_is_call;
  logic [riscv_pkg::VADDR_W-1: 1]                    f2_call_target_vaddr;
  scariv_ic_pkg::ic_block_t       f2_is_ret;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W-1: 0]         f2_ras_be;
  logic [riscv_pkg::VADDR_W-1: 1]                    f2_ras_vaddr;
  scariv_predict_pkg::ras_idx_t     f2_ras_index;

  modport master (
    output f1_is_call,
    output f1_is_ret,
    output f1_ras_vaddr,
    output f1_ras_index,
    output f2_is_call,
    output f2_call_target_vaddr,
    output f2_is_ret,
    output f2_ras_be,
    output f2_ras_vaddr,
    output f2_ras_index
  );

  modport slave (
    input f1_is_call,
    input f1_is_ret,
    input f1_ras_vaddr,
    input f1_ras_index,
    input f2_is_call,
    input f2_call_target_vaddr,
    input f2_is_ret,
    input f2_ras_be,
    input f2_ras_vaddr,
    input f2_ras_index
  );

endinterface // bim_search_if


interface gshare_search_if;

  logic                  f0_valid;
  scariv_pkg::vaddr_t      f0_pc_vaddr;

  logic                                                                            f2_valid;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0]                                   f2_pred_taken;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][ 1: 0]                            f2_bim_value;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][scariv_pkg::GSHARE_BHT_W-1: 0]    f2_index;
  logic [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0][scariv_pkg::GSHARE_HIST_LEN-1: 0] f2_bhr;

  modport master (
    output f0_valid,
    output f0_pc_vaddr,
    input  f2_valid,
    input  f2_pred_taken,
    input  f2_bim_value,
    input  f2_index,
    input  f2_bhr
  );

  modport slave (
    input  f0_valid,
    input  f0_pc_vaddr,
    output f2_valid,
    output f2_pred_taken,
    output f2_bim_value,
    output f2_index,
    output f2_bhr
  );

  modport monitor (
    input f2_valid,
    input f2_index,
    input f2_pred_taken,
    input f2_bim_value,
    input f2_bhr
  );


endinterface // gshare_search_if

interface ubtb_search_if;
  logic                           predict_valid;
  scariv_predict_pkg::ubtb_info_t ubtb_info;

  modport master (output predict_valid, ubtb_info);
  modport slave  (input  predict_valid, ubtb_info);
endinterface // ubtb_search_if
