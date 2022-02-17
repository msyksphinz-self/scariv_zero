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
                            1 +              // CSU
                            FPU_INST_NUM;    // FPU
  localparam TGT_BUS_SIZE = REL_BUS_SIZE;
  localparam CMT_BUS_SIZE = ALU_INST_NUM +   // ALU
                            LSU_INST_NUM +   // LSU
                            1 +              // BRU
                            1 +              // CSU
                            FPU_INST_NUM;    // FPU

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

  localparam INT_REGPORT_NUM = msrh_conf_pkg::LSU_INST_NUM * 2 +    // ALU port
                               msrh_conf_pkg::ALU_INST_NUM * 2 +    // LSU port
                               2 +                                  // BRU port
                               1 +                                  // CSR port
                               msrh_conf_pkg::FPU_INST_NUM;         // FPU port

  localparam FP_REGPORT_NUM = 3 * msrh_conf_pkg::FPU_INST_NUM;

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
  ECALL_M             = 11,
  INST_PAGE_FAULT     = 12,
  LOAD_PAGE_FAULT     = 13,
  STAMO_PAGE_FAULT    = 15,

  MRET = 24,
  SRET = 25,
  URET = 26,
  SILENT_FLUSH = 27,
  ANOTHER_FLUSH = 28
} except_t;

typedef struct packed {
  logic              valid;
  reg_t              typ;
  logic [4:0]        regidx;
  logic [RNID_W-1:0] rnid;
  logic              ready;
} reg_rd_disp_t;

typedef struct packed {
    logic              valid;
    reg_t              typ;
    logic [4:0]        regidx;
    logic [RNID_W-1:0] rnid;
    logic [RNID_W-1:0] old_rnid;
} reg_wr_disp_t;

  typedef struct packed {
    logic valid;
    logic illegal_valid; // decode error: illegal instruction
    logic [31:0] inst;

    logic          rvc_inst_valid;
    logic [15: 0]  rvc_inst;

    logic [riscv_pkg::VADDR_W-1:0] pc_addr;
    inst_cat_t   cat;
    logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0] brtag;
    logic [msrh_conf_pkg::RV_BRU_ENTRY_SIZE-1:0]         br_mask;

    // logic [2:0] op;
    // logic imm;
    // logic size;
    // logic sign;

    logic                           is_call;
    logic                           is_ret;
    logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] ras_index;
    logic [riscv_pkg::VADDR_W-1: 0]                    ras_prev_vaddr;
    logic                           pred_taken;
    logic [ 1: 0]                   bim_value;
    logic                           btb_valid;
    logic [riscv_pkg::VADDR_W-1: 0] pred_target_vaddr;

    reg_wr_disp_t         wr_reg;
    reg_rd_disp_t [ 2: 0] rd_regs;
  } disp_t;


  typedef struct packed {
    logic [ALU_INST_NUM-1: 0][$clog2(ARITH_DISP_SIZE): 0] alu_inst_cnt;
    logic [$clog2(MULDIV_DISP_SIZE): 0]                   muldiv_inst_cnt;
    logic [LSU_INST_NUM-1: 0][$clog2(MEM_DISP_SIZE): 0]   lsu_inst_cnt;
    logic [$clog2(LDQ_SIZE): 0]                           ld_inst_cnt;
    logic [$clog2(STQ_SIZE): 0]                           st_inst_cnt;
    logic [$clog2(BRU_DISP_SIZE): 0]                      bru_inst_cnt;
    logic [$clog2(CSU_DISP_SIZE): 0]                      csu_inst_cnt;
    logic [$clog2(FPU_DISP_SIZE): 0]                      fpu_inst_cnt;
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

    ret.wr_reg.rnid     = rd_rnid;
    ret.wr_reg.old_rnid = rd_old_rnid;
    ret.rd_regs[0].ready   = rs1_active;
    ret.rd_regs[0].rnid    = rs1_rnid;
    ret.rd_regs[1].ready   = rs2_active;
    ret.rd_regs[1].rnid    = rs2_rnid;
    ret.brtag       = brtag;
    ret.br_mask     = br_mask;

    return ret;

  endfunction  // assign_disp_rename


  function disp_t merge_disp_if (disp_t int_disp,
                                 disp_t fp_disp);
    disp_t ret;
    ret = int_disp;
    ret.wr_reg = int_disp.wr_reg.typ == GPR ? int_disp.wr_reg : fp_disp.wr_reg;
    ret.rd_regs[0] = int_disp.rd_regs[0].typ == GPR ? int_disp.rd_regs[0] : fp_disp.rd_regs[0];
    ret.rd_regs[1] = int_disp.rd_regs[1].typ == GPR ? int_disp.rd_regs[1] : fp_disp.rd_regs[1];
    ret.rd_regs[2] = int_disp.rd_regs[2].typ == GPR ? int_disp.rd_regs[2] : fp_disp.rd_regs[2];

    return ret;

  endfunction  // assign_disp_rename

  typedef struct packed {
    logic [msrh_conf_pkg::DISP_SIZE-1:0]                         upd_valid;
    logic [msrh_conf_pkg::DISP_SIZE-1:0][riscv_pkg::VADDR_W-1:0] upd_br_vaddr;
    logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0]         brtag;

`ifdef SIMULATION
  logic                                                          mispredicted;
  logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0]             ras_index;
  logic [riscv_pkg::VADDR_W-1: 0]                                pred_vaddr;
`endif // SIMULATION
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
    logic [msrh_conf_pkg::DISP_SIZE-1: 0]  flush_valid;
    // Branch update info
    logic                               is_br_included;

    br_upd_info_t br_upd_info;
`ifdef SIMULATION
    logic [msrh_conf_pkg::DISP_SIZE-1:0][31: 0] lifetime;
`endif // SIMULATION
  } rob_entry_t;

typedef struct packed {
  logic              valid;
  reg_t              typ;
  logic [4:0]        regidx;
  logic [RNID_W-1:0] rnid;
} reg_wr_issue_t;

typedef struct packed {
  logic              valid;
  reg_t              typ;
  logic [4:0]        regidx;
  logic [RNID_W-1:0] rnid;
  logic              ready;
  logic              predict_ready;
} reg_rd_issue_t;

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

    logic                   is_call;
    logic                   is_ret;
    logic [$clog2(msrh_conf_pkg::RAS_ENTRY_SIZE)-1: 0] ras_index;
    logic                           pred_taken;
    logic [ 1: 0]                   bim_value;
    logic                           btb_valid;
    logic [riscv_pkg::VADDR_W-1: 0] pred_target_vaddr;

    reg_wr_issue_t         wr_reg;
    reg_rd_issue_t [ 1: 0] rd_regs;

    logic                          except_valid;
    except_t                       except_type;
    logic [riscv_pkg::XLEN_W-1: 0] except_tval;
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

  ret.is_call          = in.is_call;
  ret.is_ret           = in.is_ret;
  ret.ras_index        = in.ras_index;
  ret.pred_taken       = in.pred_taken;
  ret.bim_value        = in.bim_value;
  ret.btb_valid        = in.btb_valid;
  ret.pred_target_vaddr = in.pred_target_vaddr;

  ret.wr_reg.valid = in.wr_reg.valid;
  ret.wr_reg.typ = in.wr_reg.typ;
  ret.wr_reg.regidx = in.wr_reg.regidx;
  ret.wr_reg.rnid = in.wr_reg.rnid;

  ret.rd_regs[0].valid = in.rd_regs[0].valid;
  ret.rd_regs[0].typ = in.rd_regs[0].typ;
  ret.rd_regs[0].regidx = in.rd_regs[0].regidx;
  ret.rd_regs[0].rnid = in.rd_regs[0].rnid;
  ret.rd_regs[0].ready = in.rd_regs[0].ready | rs1_rel_hit & ~rs1_may_mispred | rs1_phy_hit;
  ret.rd_regs[0].predict_ready = rs1_rel_hit & rs1_may_mispred;

  ret.rd_regs[1].valid = in.rd_regs[1].valid;
  ret.rd_regs[1].regidx = in.rd_regs[1].regidx;
  ret.rd_regs[1].typ = in.rd_regs[1].typ;
  ret.rd_regs[1].rnid = in.rd_regs[1].rnid;
  ret.rd_regs[1].ready = in.rd_regs[1].ready | rs2_rel_hit & ~rs2_may_mispred | rs2_phy_hit;
  ret.rd_regs[1].predict_ready = rs2_rel_hit & rs2_may_mispred;

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

// For flushing another instruction
typedef struct packed {
  logic                                valid;
  logic [CMT_ID_W-1:0]                 cmt_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;
} another_flush_t;

// -----------------
// Commit Signals
// -----------------
typedef struct packed {
  logic                 commit;
  logic [CMT_ID_W-1:0] cmt_id;
  logic [DISP_SIZE-1:0] grp_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] except_valid;
  except_t                        except_type;
  logic [riscv_pkg::VADDR_W-1: 0] epc;
  logic [riscv_pkg::XLEN_W-1: 0]  tval;
  logic [DISP_SIZE-1:0]           dead_id;
  // logic                           all_dead;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] flush_valid;
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
  return commit.commit & (|commit.flush_valid);
endfunction // is_flushed_commit

function inst0_older (logic inst0_vld, logic [CMT_ID_W-1:0] inst0_cmt_id, logic [DISP_SIZE-1: 0] inst0_grp_id,
                      logic inst1_vld, logic [CMT_ID_W-1:0] inst1_cmt_id, logic [DISP_SIZE-1: 0] inst1_grp_id);

logic                                     inst0_cmt_id_older;
logic                                     inst0_grp_id_older;

  inst0_cmt_id_older = inst0_cmt_id[msrh_pkg::CMT_ID_W-1]   ^ inst1_cmt_id[msrh_pkg::CMT_ID_W-1] ?
                       inst0_cmt_id[msrh_pkg::CMT_ID_W-2:0] > inst1_cmt_id[msrh_pkg::CMT_ID_W-2:0] :
                       inst0_cmt_id[msrh_pkg::CMT_ID_W-2:0] < inst1_cmt_id[msrh_pkg::CMT_ID_W-2:0] ;
  inst0_grp_id_older = inst0_cmt_id_older ||
                       (inst0_cmt_id == inst1_cmt_id && (inst0_grp_id < inst1_grp_id));

  return inst0_vld & inst1_vld & inst0_grp_id_older;

endfunction // inst0_older

function logic is_commit_flush_target(logic [CMT_ID_W-1:0] entry_cmt_id,
                                      logic [DISP_SIZE-1: 0] entry_grp_id,
                                      commit_blk_t commit);
  logic w_cmt_is_older;
  logic entry_older;

  w_cmt_is_older = commit.cmt_id[msrh_pkg::CMT_ID_W-1]   ^ entry_cmt_id[msrh_pkg::CMT_ID_W-1] ?
                   commit.cmt_id[msrh_pkg::CMT_ID_W-2:0] > entry_cmt_id[msrh_pkg::CMT_ID_W-2:0] :
                   commit.cmt_id[msrh_pkg::CMT_ID_W-2:0] < entry_cmt_id[msrh_pkg::CMT_ID_W-2:0] ;
  entry_older = w_cmt_is_older ||
                (commit.cmt_id == entry_cmt_id && |(commit.flush_valid & (entry_grp_id-1)));

  return is_flushed_commit(commit) & entry_older;

endfunction // is_commit_flush_target


function logic is_br_flush_target(logic [msrh_conf_pkg::RV_BRU_ENTRY_SIZE-1:0] entry_br_mask,
                                  logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1: 0] brtag,
                                  logic br_dead,
                                  logic br_mispredicted);
  return |(entry_br_mask & (1 << brtag)) & (br_dead | br_mispredicted);

endfunction // is_br_flush_target

// RNID Update signals
typedef struct packed {
  logic                                                      commit;
  logic [msrh_conf_pkg::DISP_SIZE-1:0]                       rnid_valid;
  logic [msrh_conf_pkg::DISP_SIZE-1:0][RNID_W-1:0] old_rnid;
  logic [msrh_conf_pkg::DISP_SIZE-1:0][RNID_W-1:0] rd_rnid;
  logic [msrh_conf_pkg::DISP_SIZE-1:0][ 4: 0]                rd_regidx;
  reg_t [msrh_conf_pkg::DISP_SIZE-1:0]                       rd_typ;
  // logic                                                      is_br_included;
  // logic                                                      upd_pc_valid;
  logic [msrh_conf_pkg::DISP_SIZE-1:0]                       except_valid;
  except_t                                                   except_type;
  logic [msrh_conf_pkg::DISP_SIZE-1:0]                       dead_id;
  // logic                                                        all_dead;
} cmt_rnid_upd_t;

localparam RAS_W = $clog2(msrh_conf_pkg::RAS_ENTRY_SIZE);

// ===================
// Fetch Target Queue
// ===================
typedef struct packed {
  logic                                                valid;
  logic                                                is_call;
  logic                                                is_ret;
  logic                                                is_rvc;
  logic [CMT_ID_W-1:0]                                 cmt_id;
  logic [DISP_SIZE-1:0]                                grp_id;
  logic [RAS_W-1: 0]                                   ras_index;
  logic [$clog2(msrh_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0] brtag;
  logic [msrh_conf_pkg::RV_BRU_ENTRY_SIZE-1:0]         br_mask;

  logic [riscv_pkg::VADDR_W-1: 0]                      pc_vaddr;
  logic [riscv_pkg::VADDR_W-1: 0]                      target_vaddr;
  logic [riscv_pkg::VADDR_W-1: 0]                      ras_prev_vaddr;
  logic                                                taken;
  logic                                                mispredict;
  logic                                                done;
  logic                                                dead;
} ftq_entry_t;

function ftq_entry_t assign_ftq_entry(logic [CMT_ID_W-1:0]  cmt_id,
                                      logic [DISP_SIZE-1:0] grp_id,
                                      disp_t inst);
  ftq_entry_t ret;

  ret.valid    = 1'b1;
  ret.pc_vaddr = inst.pc_addr;
  ret.ras_prev_vaddr = inst.ras_prev_vaddr;
  ret.is_call  = inst.is_call;
  ret.is_ret   = inst.is_ret;
  ret.is_rvc   = inst.rvc_inst_valid;
  ret.cmt_id   = cmt_id;
  ret.grp_id   = grp_id;
  ret.ras_index = inst.ras_index;
  ret.brtag     = inst.brtag;
  ret.br_mask   = inst.br_mask;

  ret.done      = 1'b0;
  ret.dead      = 1'b0;

  return ret;

endfunction // assign_ftq_entry

endpackage

`default_nettype wire
