`default_nettype none

package msrh_pkg;
  import riscv_pkg::*;

  localparam PC_INIT_VAL = 'h8000_0000;

  localparam INST_BUF_SIZE = 4;

  localparam DISP_SIZE = 5;

  localparam ALU_INST_NUM = 2;
  localparam LSU_INST_NUM = 2;

  localparam ARITH_DISP_SIZE = 4;
  localparam MEM_DISP_SIZE = 4;

  localparam RV_ALU_ENTRY_SIZE = 32;

  localparam REL_BUS_SIZE = ALU_INST_NUM + LSU_INST_NUM;
  localparam TGT_BUS_SIZE = REL_BUS_SIZE;
  localparam CMT_BUS_SIZE = REL_BUS_SIZE;

  localparam FLIST_SIZE = 32;
  localparam RNID_SIZE = FLIST_SIZE * DISP_SIZE;
  localparam RNID_W = $clog2(RNID_SIZE);

  localparam CMT_BLK_SIZE = 64;
  localparam CMT_BLK_W = $clog2(CMT_BLK_SIZE);

  localparam LRQ_ENTRY_SIZE = 8;

  typedef struct packed {
    logic valid;
    logic [31:0] inst;
  } inst_buf_t;

  typedef enum logic [1:0] {
    NONE,
    CAT_ARITH,
    CAT_MEM
  } inst_cat_t;

  typedef enum {
    GPR,
    FPR
  } reg_t;

  typedef struct packed {
    logic valid;
    logic [31:0] inst;
    logic [riscv_pkg::VADDR_W-1:0] pc_addr;

    logic [2:0] op;
    logic imm;
    logic size;
    logic sign;

    logic rd_valid;
    reg_t rd_type;
    logic [4:0] rd_regidx;
    logic [msrh_pkg::RNID_W-1:0] rd_rnid;

    logic rs1_valid;
    reg_t rs1_type;
    logic [4:0] rs1_regidx;
    logic [msrh_pkg::RNID_W-1:0] rs1_rnid;
    logic rs1_ready;

    logic rs2_valid;
    logic [4:0] rs2_regidx;
    reg_t rs2_type;
    logic [msrh_pkg::RNID_W-1:0] rs2_rnid;
    logic rs2_ready;

  } disp_t;

  function disp_t assign_disp_rename (disp_t disp,
                                    logic [RNID_W-1: 0] rd_rnid,
                                    logic               rs1_active,
                                    logic [RNID_W-1: 0] rs1_rnid,
                                    logic               rs2_active,
                                    logic [RNID_W-1: 0] rs2_rnid);
    disp_t ret;
    ret = disp;

    ret.rd_rnid = rd_rnid;
    ret.rs1_ready = rs1_active;
    ret.rs1_rnid = rs1_rnid;
    ret.rs2_ready = rs2_active;
    ret.rs2_rnid = rs2_rnid;

    return ret;

  endfunction  // assign_disp_rename

  typedef struct packed {
    logic [riscv_pkg::VADDR_W-1: 1] pc_addr;
    logic [msrh_pkg::DISP_SIZE-1:0] grp_id;

    msrh_pkg::disp_t[msrh_pkg::DISP_SIZE-1:0] inst;

    logic [msrh_pkg::DISP_SIZE-1:0] done_grp_id;
    logic [msrh_pkg::DISP_SIZE-1:0] old_rd_valid;
    logic [msrh_pkg::DISP_SIZE-1:0][msrh_pkg::RNID_W-1:0] old_rd_rnid;
  } rob_entry_t;

  typedef struct packed {
    logic valid;
    logic [riscv_pkg::VADDR_W-1:0] pc_addr;
    logic [31:0] inst;

    logic rd_valid;
    reg_t rd_type;
    logic [4:0] rd_regidx;
    logic [msrh_pkg::RNID_W-1:0] rd_rnid;

    logic rs1_valid;
    reg_t rs1_type;
    logic [4:0] rs1_regidx;
    logic [msrh_pkg::RNID_W-1:0] rs1_rnid;
    logic rs1_ready;

    logic rs2_valid;
    logic [4:0] rs2_regidx;
    reg_t rs2_type;
    logic [msrh_pkg::RNID_W-1:0] rs2_rnid;
    logic rs2_ready;
  } issue_t;


function issue_t assign_issue_t(disp_t in, logic rs1_hit, logic rs2_hit);
  issue_t ret;

  ret.valid = in.valid;
  ret.inst = in.inst;
  ret.pc_addr = in.pc_addr;

  ret.rd_valid = in.rd_valid;
  ret.rd_type = in.rd_type;
  ret.rd_regidx = in.rd_regidx;
  ret.rd_rnid = in.rd_rnid;

  ret.rs1_valid = in.rs1_valid;
  ret.rs1_type = in.rs1_type;
  ret.rs1_regidx = in.rs1_regidx;
  ret.rs1_rnid = in.rs1_rnid;
  ret.rs1_ready = in.rs1_ready | rs1_hit;

  ret.rs2_valid = in.rs2_valid;
  ret.rs2_regidx = in.rs2_regidx;
  ret.rs2_type = in.rs2_type;
  ret.rs2_rnid = in.rs2_rnid;
  ret.rs2_ready = in.rs2_ready | rs1_hit;

  return ret;

endfunction  // assign_issue_t


  typedef struct packed {
    logic valid;
    logic [msrh_pkg::RNID_W-1:0] rd_rnid;
    reg_t rd_type;
  } early_wr_t;

  typedef struct packed {
    logic valid;
    logic [msrh_pkg::RNID_W-1:0] rd_rnid;
    reg_t rd_type;
    logic [riscv_pkg::XLEN_W-1:0] rd_data;
  } phy_wr_t;

  typedef struct packed {
    logic                 valid;
    logic [CMT_BLK_W-1:0] cmt_id;
    logic [DISP_SIZE-1:0] grp_id;
    logic                 exc_vld;
  } done_rpt_t;

endpackage

`default_nettype wire
