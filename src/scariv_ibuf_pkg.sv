// ------------------------------------------------------------------------
// NAME : SCARIV Inst-Buffer Package
// TYPE : package
// ------------------------------------------------------------------------
// Instruction Buffer packages
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

package scariv_ibuf_pkg;

typedef struct packed {
  logic             pred_taken;
  logic [1:0]       bim_value;
  logic             btb_valid;
  logic             is_cond;
  scariv_pkg::vaddr_t pred_target_vaddr;
  scariv_pkg::gshare_bht_t gshare_index;
  scariv_pkg::gshare_bht_t gshare_bhr;
} pred_info_t;


typedef struct packed {
  logic                           is_call;
  logic                           is_ret;
  logic [$clog2(scariv_conf_pkg::RAS_ENTRY_SIZE)-1: 0] ras_index;
  scariv_pkg::vaddr_t                    pred_target_vaddr;
} ras_info_t;


typedef struct packed {
  logic                                      valid;
  logic                                      dead;
  logic [riscv_pkg::VADDR_W-1: 1]            pc;
  scariv_pkg::ic_data_t                      data;
  scariv_pkg::ic_strb_t                      byte_en;
  logic                                      tlb_except_valid;
  scariv_pkg::except_t                       tlb_except_cause;

  pred_info_t [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] pred_info;
  ras_info_t  [scariv_lsu_pkg::ICACHE_DATA_B_W/2-1: 0] ras_info;
`ifdef SIMULATION
  scariv_pkg::vaddr_t pc_dbg;
`endif // SIMULATION
  logic               int_inserted;
} inst_buf_t;


endpackage // scariv_ibuf_pkg
