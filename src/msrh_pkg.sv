`default_nettype none

package msrh_pkg;
  import riscv_pkg::*;
  import msrh_conf_pkg::*;

  import decoder_inst_cat_pkg::*;

  integer STDERR = 32'h8000_0002;

  localparam PC_INIT_VAL = 'h8000_0000;

  localparam INST_BUF_SIZE = 4;

  localparam REL_BUS_SIZE = ALU_INST_NUM +
                            LSU_INST_NUM +
                            1 +              // BRU
                            1;               // CSU
  localparam TGT_BUS_SIZE = REL_BUS_SIZE;
  localparam CMT_BUS_SIZE = ALU_INST_NUM +   // ALU
                            2 +              // LSU
                            1 +              // BRU
                            1;               // CSU

  localparam FLIST_SIZE = 32;
  localparam RNID_SIZE = FLIST_SIZE * DISP_SIZE + 32;
  localparam RNID_W = $clog2(RNID_SIZE);

  localparam CMT_ENTRY_W = $clog2(CMT_ENTRY_SIZE);

  localparam CMT_ID_SIZE = CMT_ENTRY_SIZE * 2;
  localparam CMT_ID_W = $clog2(CMT_ID_SIZE);

  localparam LRQ_NORM_ENTRY_SIZE = 6;
  localparam LRQ_ST_ENTRY_SIZE = 2;
  localparam LRQ_ENTRY_SIZE = LRQ_NORM_ENTRY_SIZE + LRQ_ST_ENTRY_SIZE;
  localparam LRQ_ENTRY_W = $clog2(LRQ_ENTRY_SIZE);

  localparam REGPORT_NUM = msrh_conf_pkg::LSU_INST_NUM * 2 +    // ALU port
                           msrh_conf_pkg::ALU_INST_NUM * 2 +    // LSU port
                           2 +                                  // BRU port
                           1;                                   // CSR port

  typedef enum logic [1:0] {
     PRV_U = 0,
     PRV_S = 1,
     PRV_M = 3
  } priv_t;

  typedef struct packed {
    logic valid;
    logic [31:0] inst;
  } inst_buf_t;

  typedef enum {
    GPR,
    FPR
  } reg_t;

// ------------------------
// Exception Control
// ------------------------
typedef enum logic [$clog2(riscv_pkg::XLEN_W)-1: 0] {
  INST_ADDR_MISALIGN = 0,
  INST_ACC_FAULT     = 1,
  ILLEGAL_INST       = 2,
  BREAKPOINT         = 3,
  LOAD_ADDR_MISALIGN = 4,
  LOAD_ACC_FAULT     = 5,
  STAMO_ADDR_MISALIGN = 6,
  STAMO_ACC_FAULT     = 7,
  ECALL_U             = 8,
  ECALL_S             = 9,
  ECALL_M             = 10,
  INST_PAGE_FAULT     = 12,
  LOAD_PAGE_FAULT     = 13,
  STAMO_PAGE_FAULT    = 15,

  MRET = 24,
  SRET = 25,
  URET = 26,
  SILENT_FLUSH = 27
} except_t;

  typedef struct packed {
    logic valid;
    logic illegal_valid; // decode error: illegal instruction
    logic [31:0] inst;

`ifdef SIMULATION
  logic          rvc_inst_valid;
  logic [15: 0]  rvc_inst;
`endif // SIMULATION

    logic [riscv_pkg::VADDR_W-1:0] pc_addr;
    inst_cat_t   cat;
    logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0] brtag;
    logic [msrh_conf_pkg::RV_BRU_ENTRY_SIZE-1:0]         br_mask;

    logic [2:0] op;
    logic imm;
    logic size;
    logic sign;

    logic rd_valid;
    reg_t rd_type;
    logic [4:0] rd_regidx;
    logic [RNID_W-1:0] rd_rnid;
    logic [RNID_W-1:0] rd_old_rnid;

    logic rs1_valid;
    reg_t rs1_type;
    logic [4:0] rs1_regidx;
    logic [RNID_W-1:0] rs1_rnid;
    logic rs1_ready;

    logic rs2_valid;
    logic [4:0] rs2_regidx;
    reg_t rs2_type;
    logic [RNID_W-1:0] rs2_rnid;
    logic rs2_ready;

  } disp_t;


  typedef struct packed {
    logic [ALU_INST_NUM-1: 0][$clog2(ARITH_DISP_SIZE): 0] alu_inst_cnt;
    logic [$clog2(MULDIV_DISP_SIZE): 0]                   muldiv_inst_cnt;
    logic [LSU_INST_NUM-1: 0][$clog2(MEM_DISP_SIZE): 0]   lsu_inst_cnt;
    logic [$clog2(LDQ_SIZE): 0]                           ld_inst_cnt;
    logic [$clog2(STQ_SIZE): 0]                           st_inst_cnt;
    logic [$clog2(BRU_DISP_SIZE): 0]                      bru_inst_cnt;
    logic [$clog2(CSU_DISP_SIZE): 0]                      csu_inst_cnt;
  } resource_cnt_t;

  function disp_t assign_disp_rename (disp_t disp,
                                      logic [RNID_W-1: 0] rd_rnid,
                                      logic [RNID_W-1: 0] rd_old_rnid,
                                      logic               rs1_active,
                                      logic [RNID_W-1: 0] rs1_rnid,
                                      logic               rs2_active,
                                      logic [RNID_W-1: 0] rs2_rnid,
                                      logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0] brtag,
                                      logic [msrh_conf_pkg::RV_BRU_ENTRY_SIZE-1:0]         br_mask
                                      );
    disp_t ret;
    ret = disp;

    ret.rd_rnid     = rd_rnid;
    ret.rd_old_rnid = rd_old_rnid;
    ret.rs1_ready   = rs1_active;
    ret.rs1_rnid    = rs1_rnid;
    ret.rs2_ready   = rs2_active;
    ret.rs2_rnid    = rs2_rnid;
    ret.brtag       = brtag;
    ret.br_mask     = br_mask;

    return ret;

  endfunction  // assign_disp_rename

  typedef struct packed {
    logic [msrh_conf_pkg::DISP_SIZE-1:0]                         upd_valid;
    logic [msrh_conf_pkg::DISP_SIZE-1:0][riscv_pkg::VADDR_W-1:0] upd_br_vaddr;
    logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0]         brtag;
  } br_upd_info_t;

  typedef struct packed {
    logic          valid;

    logic [riscv_pkg::VADDR_W-1: 1] pc_addr;
    logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;

    disp_t[msrh_conf_pkg::DISP_SIZE-1:0] inst;

    logic [msrh_conf_pkg::DISP_SIZE-1:0] done_grp_id;

    logic [msrh_conf_pkg::DISP_SIZE-1:0]   except_valid;
    except_t [msrh_conf_pkg::DISP_SIZE-1:0] except_type;
    logic [msrh_conf_pkg::DISP_SIZE-1:0][riscv_pkg::XLEN_W-1:0] except_tval;

    logic [msrh_conf_pkg::DISP_SIZE-1: 0]  dead;
    // Branch update info
    logic                               is_br_included;
    br_upd_info_t br_upd_info;
  } rob_entry_t;

  typedef struct packed {
    logic valid;
    logic [riscv_pkg::VADDR_W-1:0] pc_addr;
    logic [31:0] inst;
    inst_cat_t   cat;
    logic        is_rvc;
    logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0] brtag;
    logic [msrh_conf_pkg::RV_BRU_ENTRY_SIZE-1:0]         br_mask;

    logic [CMT_ID_W-1:0] cmt_id;
    logic [DISP_SIZE-1:0] grp_id;

    logic rd_valid;
    reg_t rd_type;
    logic [4:0] rd_regidx;
    logic [RNID_W-1:0] rd_rnid;

    logic rs1_valid;
    reg_t rs1_type;
    logic [4:0] rs1_regidx;
    logic [RNID_W-1:0] rs1_rnid;
    logic rs1_ready;
    logic rs1_pred_ready;

    logic rs2_valid;
    logic [4:0] rs2_regidx;
    reg_t rs2_type;
    logic [RNID_W-1:0] rs2_rnid;
    logic rs2_ready;
    logic rs2_pred_ready;

    logic             except_valid;
    except_t except_type;
  } issue_t;


function issue_t assign_issue_t(disp_t in,
                                logic [CMT_ID_W-1:0] cmt_id,
                                logic [DISP_SIZE-1:0] grp_id,
                                logic rs1_rel_hit, logic rs2_rel_hit,
                                logic rs1_phy_hit, logic rs2_phy_hit,
                                logic rs1_may_mispred, logic rs2_may_mispred);
  issue_t ret;

  ret.valid = in.valid;
  ret.inst = in.inst;
  ret.pc_addr = in.pc_addr;

  ret.cat = in.cat;
  ret.is_rvc = in.rvc_inst_valid;

  ret.brtag   = in.brtag;
  ret.br_mask = in.br_mask;

  ret.cmt_id = cmt_id;
  ret.grp_id = grp_id;

  ret.rd_valid = in.rd_valid;
  ret.rd_type = in.rd_type;
  ret.rd_regidx = in.rd_regidx;
  ret.rd_rnid = in.rd_rnid;

  ret.rs1_valid = in.rs1_valid;
  ret.rs1_type = in.rs1_type;
  ret.rs1_regidx = in.rs1_regidx;
  ret.rs1_rnid = in.rs1_rnid;
  ret.rs1_ready = in.rs1_ready | rs1_rel_hit & ~rs1_may_mispred | rs1_phy_hit;
  ret.rs1_pred_ready = rs1_rel_hit & rs1_may_mispred;

  ret.rs2_valid = in.rs2_valid;
  ret.rs2_regidx = in.rs2_regidx;
  ret.rs2_type = in.rs2_type;
  ret.rs2_rnid = in.rs2_rnid;
  ret.rs2_ready = in.rs2_ready | rs2_rel_hit & ~rs2_may_mispred | rs2_phy_hit;
  ret.rs2_pred_ready = rs2_rel_hit & rs2_may_mispred;

  ret.except_valid = 1'b0;
  ret.except_type  = INST_ADDR_MISALIGN;
  return ret;

endfunction  // assign_issue_t

  typedef enum logic [ 2: 0] { INIT, WAIT, ISSUED, DONE, WAIT_COMPLETE, DEAD } sched_state_t;

  typedef struct packed {
    logic valid;
    logic [RNID_W-1:0] rd_rnid;
    reg_t rd_type;

    logic                        may_mispred;
  } early_wr_t;

  typedef struct packed {
    logic valid;
    logic [RNID_W-1:0] rd_rnid;
    reg_t rd_type;
    logic [riscv_pkg::XLEN_W-1:0] rd_data;
  } phy_wr_t;

  typedef struct packed {
    logic               mis_valid;     // Mispredict
    reg_t               rd_type;
    logic [RNID_W-1: 0] rd_rnid;
  } mispred_t;


  typedef struct packed {
    logic                 valid;
    logic [CMT_ID_W-1:0]  cmt_id;
    logic [DISP_SIZE-1:0] grp_id;
    logic                 except_valid;
    except_t              except_type;
    logic [riscv_pkg::XLEN_W-1: 0] except_tval;
  } done_rpt_t;

// -----------------
// Commit Signals
// -----------------
typedef struct packed {
  logic                 commit;
  logic [CMT_ID_W-1:0] cmt_id;
  logic [DISP_SIZE-1:0] grp_id;
  // logic                           upd_pc_valid;
  // logic [riscv_pkg::VADDR_W-1: 0] upd_pc_vaddr;
  // logic                           flush_valid;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] except_valid;
  except_t                        except_type;
  logic                           fence_i;
  logic [riscv_pkg::VADDR_W-1: 0] epc;
  logic [riscv_pkg::XLEN_W-1: 0]  tval;
  logic [DISP_SIZE-1:0]           dead_id;
  logic                           all_dead;
} commit_blk_t;

function logic [$clog2(DISP_SIZE)-1: 0] encoder_grp_id (logic[DISP_SIZE-1: 0] in);
  for (int i = 0; i < DISP_SIZE; i++) begin
    /* verilator lint_off WIDTH */
    if (in[i]) return i;
  end
  /* verilator lint_off WIDTH */
  return 'hx;
endfunction // encoder_grp_id

function logic is_flushed_commit (commit_blk_t commit);
  return commit.commit & (|commit.except_valid) & ~commit.all_dead;
endfunction // is_flushed_commit

function logic is_commit_flush_target(logic [CMT_ID_W-1:0] entry_cmt_id,
                                      logic [DISP_SIZE-1: 0] entry_grp_id,
                                      commit_blk_t commit);
  return commit.commit & (|commit.except_valid) &
         ~((entry_cmt_id == commit.cmt_id) & ~|(entry_grp_id & commit.dead_id)) &
         ~commit.all_dead;

endfunction // is_commit_flush_target


function logic is_br_flush_target(logic [msrh_conf_pkg::RV_BRU_ENTRY_SIZE-1:0] entry_br_mask,
                                  logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1: 0] brtag);
  return |(entry_br_mask & (1 << brtag));

endfunction // is_br_flush_target

// RNID Update signals
typedef struct packed {
  logic                                                      commit;
  logic [msrh_conf_pkg::DISP_SIZE-1:0]                       rnid_valid;
  logic [msrh_conf_pkg::DISP_SIZE-1:0][RNID_W-1:0] old_rnid;
  logic [msrh_conf_pkg::DISP_SIZE-1:0][RNID_W-1:0] rd_rnid;
  logic [msrh_conf_pkg::DISP_SIZE-1:0][ 4: 0]                rd_regidx;
  // logic                                                      is_br_included;
  // logic                                                      upd_pc_valid;
  logic [msrh_conf_pkg::DISP_SIZE-1:0]                       except_valid;
  except_t                                                   except_type;
  logic [msrh_conf_pkg::DISP_SIZE-1:0]                       dead_id;
  logic                                                      all_dead;
} cmt_rnid_upd_t;

endpackage

`default_nettype wire
