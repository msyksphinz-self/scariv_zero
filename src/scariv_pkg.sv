// ------------------------------------------------------------------------
// NAME : scariv_pkg
// TYPE : package
// ------------------------------------------------------------------------
// SCARIV Main Package
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

`default_nettype none

package scariv_pkg;
  import riscv_pkg::*;
  import scariv_conf_pkg::*;

  import decoder_inst_cat_pkg::*;

  integer STDERR = 32'h8000_0002;

  localparam PC_INIT_VAL = 'h0000_1000;

  localparam INST_BUF_SIZE = scariv_conf_pkg::INST_BUF_SIZE;

  localparam MAX_ADDR_W = VADDR_W > PADDR_W ? VADDR_W : PADDR_W;

  localparam REL_BUS_SIZE = ALU_INST_NUM +
                            LSU_INST_NUM +
                            1 +              // BRU
                            1 +              // CSU
                            FPU_INST_NUM;    // FPU: Now rel is only FPU Move Port
  localparam TGT_BUS_SIZE = ALU_INST_NUM +
                            LSU_INST_NUM +
                            1 +               // BRU
                            1 +               // CSU
                            FPU_INST_NUM * 2; // FPU
  localparam CMT_BUS_SIZE = ALU_INST_NUM +    // ALU
                            LSU_INST_NUM +    // LSU
                            1 +               // BRU
                            1 +               // CSU
                            FPU_INST_NUM * 2; // FPU

  localparam FLIST_SIZE = CMT_ENTRY_SIZE;
  localparam RNID_SIZE = FLIST_SIZE * DISP_SIZE + 32;
  localparam RNID_W = $clog2(RNID_SIZE);

  localparam CMT_ENTRY_W = $clog2(CMT_ENTRY_SIZE);

  localparam CMT_ID_SIZE = CMT_ENTRY_SIZE * 2;
  localparam CMT_ID_W = $clog2(CMT_ID_SIZE);

  localparam MISSU_ENTRY_SIZE = 8;
  localparam MISSU_ENTRY_W = $clog2(MISSU_ENTRY_SIZE);

  localparam INT_REGRD_PORT_NUM = scariv_conf_pkg::ALU_INST_NUM * 2 +    // ALU port
                                  scariv_conf_pkg::LSU_INST_NUM + 1 +    // LSU port
                                  2 +                                    // BRU port
                                  1 +                                    // CSR port
                                  scariv_conf_pkg::FPU_INST_NUM;         // FPU port

  localparam FP_REGRD_PORT_NUM = scariv_conf_pkg::FPU_INST_NUM * 3 +     // FPU port
                                 1;                                      // LSU port

  localparam INT_REGWR_PORT_NUM = scariv_conf_pkg::ALU_INST_NUM +    // ALU port
                                  scariv_conf_pkg::LSU_INST_NUM +    // LSU port
                                  2 +                                // BRU port
                                  1 +                                // CSR port
                                  scariv_conf_pkg::FPU_INST_NUM * 2; // FPU port

  localparam FP_REGWR_PORT_NUM = scariv_conf_pkg::LSU_INST_NUM +     // LSU port
                                 scariv_conf_pkg::FPU_INST_NUM * 2;  // FPU port

localparam RAS_W    = $clog2(scariv_conf_pkg::RAS_ENTRY_SIZE);
localparam GSHARE_BHT_W = scariv_conf_pkg::GSHARE_BHT_W;

typedef logic [GSHARE_BHT_W-1: 0] gshare_bht_t;

localparam ALEN_W = riscv_pkg::XLEN_W > riscv_fpu_pkg::FLEN_W ? riscv_pkg::XLEN_W : riscv_fpu_pkg::FLEN_W;
typedef logic [ALEN_W-1: 0]   alen_t;
typedef logic [ALEN_W/8-1: 0] alenb_t;

typedef logic [riscv_pkg::VADDR_W-1: 0] vaddr_t;
typedef logic [riscv_pkg::PADDR_W-1: 0] paddr_t;
typedef logic [MAX_ADDR_W-1: 0]         maxaddr_t;

typedef logic [CMT_ID_W-1: 0]  cmt_id_t;
typedef logic [DISP_SIZE-1: 0] grp_id_t;
typedef logic [RNID_W-1: 0]    rnid_t;
typedef logic [$clog2(scariv_conf_pkg::RV_BRU_ENTRY_SIZE)-1:0] brtag_t;

// ICache Data Types
typedef logic [$clog2(scariv_conf_pkg::ICACHE_WAYS)-1: 0] ic_ways_idx_t;
typedef logic [scariv_conf_pkg::ICACHE_WAYS-1 : 0]    ic_ways_t;
typedef logic [scariv_conf_pkg::ICACHE_DATA_W-1: 0]   ic_data_t;
typedef logic [scariv_conf_pkg::ICACHE_DATA_W/8-1: 0] ic_strb_t;

  typedef struct packed {
    logic valid;
    logic [31:0] inst;
  } inst_buf_t;

  typedef enum logic {
    GPR,
    FPR
  } reg_t;

typedef struct packed {
  logic          nx;  // Inexact
  logic          uf;  // Underflow
  logic          of;  // Overflow
  logic          dz;  // Divide by Zero
  logic          nv;  // Invalid Operation
} fflags_t;

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
  rnid_t rnid;
  logic              ready;
} reg_rd_disp_t;

typedef struct packed {
    logic              valid;
    reg_t              typ;
    logic [4:0]        regidx;
    rnid_t rnid;
    rnid_t old_rnid;
} reg_wr_disp_t;

  typedef struct packed {
    logic valid;
    logic illegal_valid; // decode error: illegal instruction
    logic [31:0] inst;

    logic          rvc_inst_valid;
    logic [15: 0]  rvc_inst;

    vaddr_t     pc_addr;
    inst_cat_t    cat;
    inst_subcat_t subcat;
    brtag_t     brtag;

    // logic [2:0] op;
    // logic imm;
    // logic size;
    // logic sign;

    logic                           is_cond;
    logic                           is_call;
    logic                           is_ret;
    logic [RAS_W-1: 0]              ras_index;
    vaddr_t                         ras_prev_vaddr;
    logic                           pred_taken;
    logic [ 1: 0]                   bim_value;
    logic                           btb_valid;
    vaddr_t                         pred_target_vaddr;

    gshare_bht_t  gshare_index;
    gshare_bht_t  gshare_bhr;

    reg_wr_disp_t         wr_reg;
    reg_rd_disp_t [ 2: 0] rd_regs;

`ifdef SIMULATION
    logic [63: 0]                     kanata_id;
`endif // SIMULATION
  } disp_t;


  typedef struct packed {
    logic [ALU_INST_NUM-1: 0][$clog2(ARITH_DISP_SIZE): 0] alu_inst_cnt;
    logic [ALU_INST_NUM-1: 0][scariv_conf_pkg::DISP_SIZE-1: 0] alu_inst_valid;
    logic [$clog2(MULDIV_DISP_SIZE): 0]                   muldiv_inst_cnt;
    logic [LSU_INST_NUM-1: 0][$clog2(MEM_DISP_SIZE): 0]   lsu_inst_cnt;
    logic [$clog2(LDQ_SIZE): 0]                           ld_inst_cnt;
    logic [$clog2(STQ_SIZE): 0]                           st_inst_cnt;
    logic [scariv_conf_pkg::DISP_SIZE-1: 0]                 lsu_inst_valid;
    logic [$clog2(BRU_DISP_SIZE): 0]                      bru_inst_cnt;
    logic [scariv_conf_pkg::DISP_SIZE-1: 0]                 bru_inst_valid;
    logic [$clog2(CSU_DISP_SIZE): 0]                      csu_inst_cnt;
    logic [scariv_conf_pkg::DISP_SIZE-1: 0]                 csu_inst_valid;
    logic [FPU_INST_NUM-1: 0][$clog2(FPU_DISP_SIZE): 0]   fpu_inst_cnt;
    logic [FPU_INST_NUM-1: 0][scariv_conf_pkg::DISP_SIZE-1: 0] fpu_inst_valid;
  } resource_cnt_t;

  function disp_t assign_disp_rename (disp_t   disp,
                                      rnid_t   rd_rnid,
                                      rnid_t   rd_old_rnid,
                                      logic    rs1_active,
                                      rnid_t   rs1_rnid,
                                      logic    rs2_active,
                                      rnid_t   rs2_rnid,
                                      logic    rs3_active,
                                      rnid_t   rs3_rnid,
                                      brtag_t  brtag
                                      );
    disp_t ret;
    ret = disp;

    ret.wr_reg.rnid     = rd_rnid;
    ret.wr_reg.old_rnid = rd_old_rnid;
    ret.rd_regs[0].ready   = rs1_active;
    ret.rd_regs[0].rnid    = rs1_rnid;
    ret.rd_regs[1].ready   = rs2_active;
    ret.rd_regs[1].rnid    = rs2_rnid;
    ret.rd_regs[2].ready   = rs3_active;
    ret.rd_regs[2].rnid    = rs3_rnid;
    ret.brtag       = brtag;

    return ret;

  endfunction  // assign_disp_rename


  function disp_t merge_scariv_front_if (disp_t int_disp,
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
    grp_id_t                         upd_valid;
    // logic [DISP_SIZE-1: 0][riscv_pkg::VADDR_W-1:0] upd_br_vaddr;
    // brtag_t        brtag;
    // gshare_bht_t   gshare_bhr;
    // gshare_bht_t   gshare_index;
    // logic          br_taken;
    // logic [ 1: 0]  bim_value;
    // logic            btb_newly_allocated;
    // logic            mispredicted;
`ifdef SIMULATION
  logic [RAS_W-1: 0] sim_ras_index;
  vaddr_t            sim_pred_vaddr;
`endif // SIMULATION
  } br_upd_info_t;

typedef enum logic [ 2: 0] {
   DEAD_NONE         = 0,
   DEAD_EXC          = 1,
   DEAD_BRANCH       = 2,
   DEAD_PREVINST     = 3,
   DEAD_ANOTHERFLUSH = 4,
   DEAD_EXT_KILL     = 5
} dead_reason_t;

typedef struct packed {
  logic              valid;
  reg_t              typ;
  logic [4:0]        regidx;
  rnid_t rnid;
} reg_wr_issue_t;

typedef struct packed {
  logic              valid;
  reg_t              typ;
  logic [4:0]        regidx;
  rnid_t rnid;
  logic              ready;
  logic              predict_ready;
} reg_rd_issue_t;

// Instruction's static information from decoder
typedef struct packed {
  logic              valid;
  vaddr_t            pc_addr;
  inst_cat_t         cat;
  inst_subcat_t      subcat;
  reg_wr_disp_t      wr_reg;
  // logic [RAS_W-1: 0] ras_index;
  // logic              is_cond;  // Conditional Branch
  // logic              is_call;  // Call
  // logic              is_ret;   // Ret
  // gshare_bht_t       gshare_bhr;
`ifdef SIMULATION
  logic              rvc_inst_valid;
  logic [15: 0]      rvc_inst;
  logic [31: 0]      inst;
  logic [63: 0]      kanata_id;
`endif // SIMULATION
} rob_static_info_t;

  typedef struct packed {
    logic          valid;

    logic [riscv_pkg::VADDR_W-1: 1] pc_addr;
    logic    cmt_id_msb;
    grp_id_t grp_id;

    rob_static_info_t [scariv_conf_pkg::DISP_SIZE-1:0] inst;
    // disp_t[scariv_conf_pkg::DISP_SIZE-1:0] inst;

    grp_id_t done_grp_id;

    grp_id_t   except_valid;
    except_t [scariv_conf_pkg::DISP_SIZE-1:0] except_type;
    riscv_pkg::xlen_t [scariv_conf_pkg::DISP_SIZE-1:0] except_tval;

    grp_id_t  dead;
    grp_id_t  flush_valid;

    // Branch update info
    logic         is_br_included;
    br_upd_info_t br_upd_info;

    grp_id_t                  fflags_update_valid;
    fflags_t [DISP_SIZE-1: 0] fflags;

    logic                                         int_inserted;
`ifdef SIMULATION
    logic [DISP_SIZE-1: 0] [31: 0] lifetime;
    dead_reason_t[scariv_conf_pkg::DISP_SIZE-1:0] sim_dead_reason;
`endif // SIMULATION
  } rob_entry_t;

  typedef struct packed {
    logic   valid;
    vaddr_t pc_addr;
    logic [31:0] inst;
    inst_cat_t   cat;
    logic        is_rvc;
    brtag_t      brtag;

    cmt_id_t cmt_id;
    grp_id_t grp_id;

    logic                   is_cond;
    logic            oldest_valid;

    logic                   is_call;
    logic                   is_ret;
    logic [RAS_W-1: 0] ras_index;
    logic                           pred_taken;
    logic [ 1: 0]                   bim_value;
    logic                           btb_valid;
    vaddr_t pred_target_vaddr;

    reg_wr_issue_t         wr_reg;
    reg_rd_issue_t [ 2: 0] rd_regs;

    logic                          except_valid;
    except_t                       except_type;
    riscv_pkg::xlen_t except_tval;

    logic      fflags_update_valid;
    fflags_t   fflags;
`ifdef SIMULATION
    logic [63: 0]                     kanata_id;
`endif // SIMULATION
  } issue_t;



function issue_t assign_issue_common (disp_t in,
                                      cmt_id_t cmt_id,
                                      grp_id_t grp_id);
  issue_t ret;

  ret.valid = in.valid;
  ret.inst = in.inst;
  ret.pc_addr = in.pc_addr;

  ret.cat = in.cat;
  ret.is_rvc = in.rvc_inst_valid;

  ret.brtag   = in.brtag;

  ret.cmt_id = cmt_id;
  ret.grp_id = grp_id;

  ret.is_cond          = in.is_cond;
  ret.oldest_valid = (in.cat == decoder_inst_cat_pkg::INST_CAT_ST) & (in.subcat == decoder_inst_cat_pkg::INST_SUBCAT_RMW) |
                     (in.cat == decoder_inst_cat_pkg::INST_CAT_CSU);

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

  ret.except_valid = 1'b0;
  ret.except_type  = INST_ADDR_MISALIGN;

  ret.fflags_update_valid = 1'b0;
  ret.fflags = 'h0;

`ifdef SIMULATION
  ret.kanata_id = in.kanata_id;
`endif // SIMULATION
  return ret;

endfunction // assign_issue_common

function issue_t assign_issue_op2 (disp_t in,
                                   cmt_id_t cmt_id,
                                   grp_id_t grp_id,
                                   logic [ 1: 0] rs_rel_hit, logic [ 1: 0] rs_phy_hit, logic [ 1: 0] rs_may_mispred);
  issue_t ret;
  ret = assign_issue_common (in, cmt_id, grp_id);

  for (int rs_idx = 0; rs_idx < 2; rs_idx++) begin
    ret.rd_regs[rs_idx].valid         = in.rd_regs[rs_idx].valid;
    ret.rd_regs[rs_idx].typ           = in.rd_regs[rs_idx].typ;
    ret.rd_regs[rs_idx].regidx        = in.rd_regs[rs_idx].regidx;
    ret.rd_regs[rs_idx].rnid          = in.rd_regs[rs_idx].rnid;
    ret.rd_regs[rs_idx].ready         = in.rd_regs[rs_idx].ready | rs_rel_hit[rs_idx] & ~rs_may_mispred[rs_idx] | rs_phy_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready = rs_rel_hit[rs_idx] & rs_may_mispred[rs_idx];
  end

  for (int rs_idx = 2; rs_idx < 3; rs_idx++) begin
    ret.rd_regs[rs_idx].valid = 1'b0;
  end

  return ret;

endfunction  // assign_issue_t


function issue_t assign_issue_op3 (disp_t in,
                                   cmt_id_t cmt_id,
                                   grp_id_t grp_id,
                                   logic [ 2: 0] rs_rel_hit, logic [ 2: 0] rs_phy_hit, logic [ 2: 0] rs_may_mispred);
  issue_t ret;
  ret = assign_issue_common (in, cmt_id, grp_id);

  for (int rs_idx = 0; rs_idx < 3; rs_idx++) begin
    ret.rd_regs[rs_idx].valid         = in.rd_regs[rs_idx].valid;
    ret.rd_regs[rs_idx].typ           = in.rd_regs[rs_idx].typ;
    ret.rd_regs[rs_idx].regidx        = in.rd_regs[rs_idx].regidx;
    ret.rd_regs[rs_idx].rnid          = in.rd_regs[rs_idx].rnid;
    ret.rd_regs[rs_idx].ready         = in.rd_regs[rs_idx].ready | rs_rel_hit[rs_idx] & ~rs_may_mispred[rs_idx] | rs_phy_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready = rs_rel_hit[rs_idx] & rs_may_mispred[rs_idx];
  end

  return ret;

endfunction  // assign_issue_t

typedef struct packed {
  logic             except_valid;
  except_t          except_type;
  riscv_pkg::xlen_t except_tval;

  // For FPU update
  logic             fflags_update_valid;
  fflags_t          fflags;
  // For flushing another instruction
  logic             another_flush_valid;
  cmt_id_t          another_flush_cmt_id;
  grp_id_t          another_flush_grp_id;
} done_payload_t;


  typedef enum logic [ 2: 0] { INIT, WAIT, ISSUED, DONE, WAIT_COMPLETE, DEAD, SCHED_CLEAR } sched_state_t;
  typedef struct packed {
    logic  valid;
    rnid_t rd_rnid;
    reg_t  rd_type;

    logic  may_mispred;
  } early_wr_t;

  typedef struct packed {
    logic  valid;
    rnid_t rd_rnid;
    reg_t  rd_type;
    alen_t rd_data;
  } phy_wr_t;

  typedef struct packed {
    logic               mis_valid;     // Mispredict
    reg_t               rd_type;
    rnid_t rd_rnid;
  } mispred_t;


  typedef struct packed {
    logic             valid;
    cmt_id_t          cmt_id;
    grp_id_t          grp_id;
    logic             except_valid;
    except_t          except_type;
    riscv_pkg::xlen_t except_tval;
    logic             fflags_update_valid;
    fflags_t          fflags;
  } done_rpt_t;

// For flushing another instruction
typedef struct packed {
  logic    valid;
  cmt_id_t cmt_id;
  grp_id_t grp_id;
} another_flush_t;

// -----------------
// Commit Signals
// -----------------
typedef struct packed {
  logic             commit;
  cmt_id_t          cmt_id;
  grp_id_t          grp_id;
  grp_id_t          except_valid;
  except_t          except_type;
  vaddr_t           epc;
  riscv_pkg::xlen_t tval;
  grp_id_t          dead_id;
  grp_id_t          flush_valid;
  logic [DISP_SIZE-1: 0] ras_update;
  logic [DISP_SIZE-1: 0][RAS_W-1: 0] ras_index;

  // Interrupt Inserted
logic                                int_valid;
} commit_blk_t;

function logic id0_is_older_than_id1 (cmt_id_t cmt_id0, grp_id_t grp_id0,
                                      cmt_id_t cmt_id1, grp_id_t grp_id1);
logic                                w_cmt_is_older;
logic                                w_0_older_than_1;

  w_cmt_is_older = cmt_id0[scariv_pkg::CMT_ID_W-1]   ^ cmt_id1[scariv_pkg::CMT_ID_W-1] ?
                   cmt_id0[scariv_pkg::CMT_ID_W-2:0] > cmt_id1[scariv_pkg::CMT_ID_W-2:0] :
                   cmt_id0[scariv_pkg::CMT_ID_W-2:0] < cmt_id1[scariv_pkg::CMT_ID_W-2:0] ;
  w_0_older_than_1 = w_cmt_is_older ||
                     (cmt_id0 == cmt_id1 && grp_id0 < grp_id1);

  return w_0_older_than_1;

endfunction // id0_is_older_than_id1


function logic [$clog2(DISP_SIZE)-1: 0] encoder_grp_id (logic[DISP_SIZE-1: 0] in);
  for (int i = 0; i < DISP_SIZE; i++) begin
    /* verilator lint_off WIDTH */
    if (in[i]) return i;
  end
  /* verilator lint_off WIDTH */
  return 'hx;
endfunction // encoder_grp_id

function logic is_flushed_commit (commit_blk_t commit);
  return commit.commit & |(commit.flush_valid & ~commit.dead_id);
endfunction // is_flushed_commit

function inst0_older (logic inst0_vld, cmt_id_t inst0_cmt_id, grp_id_t inst0_grp_id,
                      logic inst1_vld, cmt_id_t inst1_cmt_id, grp_id_t inst1_grp_id);

logic                                     inst0_cmt_id_older;
logic                                     inst0_grp_id_older;

  inst0_cmt_id_older = inst0_cmt_id[CMT_ID_W-1]   ^ inst1_cmt_id[CMT_ID_W-1] ?
                       inst0_cmt_id[CMT_ID_W-2:0] > inst1_cmt_id[CMT_ID_W-2:0] :
                       inst0_cmt_id[CMT_ID_W-2:0] < inst1_cmt_id[CMT_ID_W-2:0] ;
  inst0_grp_id_older = inst0_cmt_id_older ||
                       (inst0_cmt_id == inst1_cmt_id && (inst0_grp_id < inst1_grp_id));

  return inst0_vld & inst1_vld & inst0_grp_id_older;

endfunction // inst0_older

function logic is_commit_flush_target(cmt_id_t entry_cmt_id,
                                      grp_id_t entry_grp_id,
                                      commit_blk_t commit);
  logic w_cmt_is_older;
  logic entry_older;

  w_cmt_is_older = commit.cmt_id[CMT_ID_W-1]   ^ entry_cmt_id[CMT_ID_W-1] ?
                   commit.cmt_id[CMT_ID_W-2:0] > entry_cmt_id[CMT_ID_W-2:0] :
                   commit.cmt_id[CMT_ID_W-2:0] < entry_cmt_id[CMT_ID_W-2:0] ;
  entry_older = w_cmt_is_older ||
                (commit.cmt_id == entry_cmt_id && |(commit.flush_valid & entry_grp_id)
                 /* |(commit.flush_valid & (entry_grp_id-1))*/);

  return is_flushed_commit(commit) & entry_older;

endfunction // is_commit_flush_target


//                                   brtag_t brtag,
//                                   logic br_dead,
//                                   logic br_mispredicted);
// logic w_cmt_is_older;
// logic entry_older;
//
// w_cmt_is_older = br_cmt_id[CMT_ID_W-1]   ^ entry_cmt_id[CMT_ID_W-1] ?
//                  br_cmt_id[CMT_ID_W-2:0] > entry_cmt_id[CMT_ID_W-2:0] :
//                  br_cmt_id[CMT_ID_W-2:0] < entry_cmt_id[CMT_ID_W-2:0] ;
// entry_older = w_cmt_is_older ||
//               (br_cmt_id == entry_cmt_id && |(br_flush_valid & entry_grp_id));
//
// endfunction // is_br_flush_target

function logic is_br_flush_target(cmt_id_t entry_cmt_id, grp_id_t entry_grp_id,
                                  cmt_id_t br_cmt_id, grp_id_t br_grp_id,
                                  logic br_dead, logic br_mispredicted);
  logic w_cmt_is_older;
  logic entry_older;

  w_cmt_is_older = br_cmt_id[CMT_ID_W-1]   ^ entry_cmt_id[CMT_ID_W-1] ?
                   br_cmt_id[CMT_ID_W-2:0] > entry_cmt_id[CMT_ID_W-2:0] :
                   br_cmt_id[CMT_ID_W-2:0] < entry_cmt_id[CMT_ID_W-2:0] ;
  entry_older = w_cmt_is_older | (br_cmt_id == entry_cmt_id) & (br_grp_id <= entry_grp_id);

  return entry_older & br_mispredicted;

endfunction // is_br_flush_target

function logic is_br_flush_target_wo_itself(cmt_id_t entry_cmt_id, grp_id_t entry_grp_id,
                                            cmt_id_t br_cmt_id, grp_id_t br_grp_id,
                                            logic br_dead, logic br_mispredicted);
logic                                             w_cmt_is_older;
  logic entry_older;

  w_cmt_is_older = br_cmt_id[CMT_ID_W-1]   ^ entry_cmt_id[CMT_ID_W-1] ?
                   br_cmt_id[CMT_ID_W-2:0] > entry_cmt_id[CMT_ID_W-2:0] :
                   br_cmt_id[CMT_ID_W-2:0] < entry_cmt_id[CMT_ID_W-2:0] ;
  entry_older = w_cmt_is_older | (br_cmt_id == entry_cmt_id) & (br_grp_id < entry_grp_id);

  return entry_older & br_mispredicted;

endfunction // is_br_flush_target

// RNID Update signals
typedef struct packed {
  logic                                                      commit;
  grp_id_t                                         rnid_valid;
  logic [scariv_conf_pkg::DISP_SIZE-1:0][RNID_W-1:0] old_rnid;
  logic [scariv_conf_pkg::DISP_SIZE-1:0][RNID_W-1:0] rd_rnid;
  logic [scariv_conf_pkg::DISP_SIZE-1:0][ 4: 0]      rd_regidx;
  reg_t [scariv_conf_pkg::DISP_SIZE-1:0]             rd_typ;
  // logic                                                      is_br_included;
  // logic                                                      upd_pc_valid;
  grp_id_t                       except_valid;
  except_t                                                   except_type;
  grp_id_t                       dead_id;
  // logic                                                        all_dead;
} cmt_rnid_upd_t;

// ===================
// Fetch Target Queue
// ===================
typedef struct packed {
  logic              valid;
  logic              is_cond;
  logic              is_call;
  logic              is_ret;
  logic              is_rvc;
  cmt_id_t           cmt_id;
  grp_id_t           grp_id;
  logic [RAS_W-1: 0] ras_index;
  brtag_t            brtag;

  logic              btb_valid; // Predicted
  logic [ 1: 0]      bim_value;

  gshare_bht_t  gshare_index;
  gshare_bht_t  gshare_bhr;

  vaddr_t pc_vaddr;
  vaddr_t target_vaddr;
  vaddr_t ras_prev_vaddr;
  logic   taken;
  logic   mispredict;
  logic   done;
  logic   notify_valid;
  logic   dead;
`ifdef SIMULATION
  vaddr_t pred_target_vaddr;
  logic [31: 0] inst;
`endif // SIMULATION

} ftq_entry_t;

function automatic ftq_entry_t assign_ftq_entry(cmt_id_t  cmt_id,
                                                grp_id_t grp_id,
                                                disp_t inst);
  ftq_entry_t ret;

  ret.valid    = 1'b1;
  ret.pc_vaddr = inst.pc_addr;
  ret.ras_prev_vaddr = inst.ras_prev_vaddr;
  ret.is_cond  = inst.is_cond;
  ret.is_call  = inst.is_call;
  ret.is_ret   = inst.is_ret;
  ret.is_rvc   = inst.rvc_inst_valid;
  ret.cmt_id   = cmt_id;
  ret.grp_id   = grp_id;
  ret.ras_index = inst.ras_index;
  ret.brtag     = inst.brtag;

  ret.btb_valid = inst.btb_valid;
  ret.bim_value = inst.bim_value;

  ret.gshare_index      = inst.gshare_index;
  ret.gshare_bhr        = inst.gshare_bhr;

  ret.notify_valid = 1'b0;
  ret.done      = 1'b0;
  ret.dead      = 1'b0;

`ifdef SIMULATION
  ret.pred_target_vaddr = inst.pred_target_vaddr;
  ret.inst = inst.inst;
`endif // SIMULATION

  return ret;

endfunction // assign_ftq_entry

typedef struct packed {
  logic   valid;
  logic [riscv_pkg::VADDR_W-1: 1] pc;
`ifdef SIMULATION
  vaddr_t pc_dbg;
`endif // SIMULATION
  logic int_inserted;
  ic_data_t inst;
  ic_strb_t byte_en;
  logic     tlb_except_valid;
  except_t  tlb_except_cause;
} inst_buffer_in_t;

endpackage

`default_nettype wire
