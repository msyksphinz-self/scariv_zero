`default_nettype none

package msrh_pkg;
  import riscv_pkg::*;

  localparam PC_INIT_VAL = 'h8000_0000;

  localparam DISP_SIZE = 5;

  localparam ALU_INST_NUM = 2;

  localparam ARITH_DISP_SIZE = 4;
  localparam MEM_DISP_SIZE = 4;

  localparam RV_ALU_ENTRY_SIZE = 32;

  localparam REL_BUS_SIZE = ALU_INST_NUM;
  localparam TGT_BUS_SIZE = REL_BUS_SIZE;
  localparam CMT_BUS_SIZE = REL_BUS_SIZE;

  localparam FLIST_SIZE = 32;
  localparam RNID_SIZE = FLIST_SIZE * DISP_SIZE;
  localparam RNID_W = $clog2(RNID_SIZE);

  localparam ICACHE_TAG_HIGH = riscv_pkg::XLEN_W;
  localparam ICACHE_TAG_LOW = 12;
  localparam ICACHE_DATA_W = 256;
  localparam ICACHE_WAY_W = 4;
  localparam ICACHE_DATA_B_W = ICACHE_DATA_W / 8;


  localparam DCACHE_TAG_HIGH = riscv_pkg::XLEN_W;
  localparam DCACHE_TAG_LOW = 12;
  localparam DCACHE_DATA_W = 256;
  localparam DCACHE_WAY_W = 4;
  localparam DCACHE_DATA_B_W = DCACHE_DATA_W / 8;

  localparam CMT_BLK_SIZE = 64;
  localparam CMT_BLK_W = $clog2(CMT_BLK_SIZE);

  localparam L2_CMD_TAG_W = 4;

  typedef struct packed {
    logic valid;
    logic [riscv_pkg::VADDR_W-1:0] vaddr;
  } ic_req_t;

  typedef struct packed {
    logic valid;
    logic [riscv_pkg::VADDR_W-1:1]      addr;
    logic [msrh_pkg::ICACHE_DATA_W-1:0] data;
    logic [msrh_pkg::ICACHE_DATA_B_W-1:0] be;
  } ic_resp_t;

  typedef enum logic [4:0] {
    M_XRD = 5'b00000,  // int load
    M_XWR = 5'b00001,  // int store
    M_PFR = 5'b00010,  // prefetch with intent to read
    M_PFW = 5'b00011,  // prefetch with intent to write
    M_XA_SWAP = 5'b00100,
    M_FLUSH_ALL = 5'b00101,  // flush all lines
    M_XLR = 5'b00110,
    M_XSC = 5'b00111,
    M_XA_ADD = 5'b01000,
    M_XA_XOR = 5'b01001,
    M_XA_OR = 5'b01010,
    M_XA_AND = 5'b01011,
    M_XA_MIN = 5'b01100,
    M_XA_MAX = 5'b01101,
    M_XA_MINU = 5'b01110,
    M_XA_MAXU = 5'b01111,
    M_FLUSH = 5'b10000,  // write back dirty data and cede R/W permissions
    M_PWR = 5'b10001,  // partial (masked) store
    M_PRODUCE = 5'b10010,  // write back dirty data and cede W permissions
    M_CLEAN = 5'b10011,  // write back dirty data and retain R/W permissions
    M_SFENCE = 5'b10100,  // flush TLB
    M_WOK = 5'b10111  // check write permissions but don't perform a write
  } mem_cmd_t;

  typedef struct packed {
    logic [riscv_pkg::PPN_W-1:0] ppn;
    logic u;
    logic g;
    logic ae;
    logic sw;
    logic sx;
    logic sr;
    logic pw;
    logic px;
    logic pr;
    logic pal;
    logic paa;
    logic eff;
    logic c;
    logic fragmented_superpage;
  } tlb_entry_data_t;

  typedef struct packed {
    logic valid;
    logic [1:0] level;
    logic [riscv_pkg::VADDR_W-1:riscv_pkg::PG_IDX_BITS] tag;
    tlb_entry_data_t [3:0] entry_data;
  } tlb_entry_t;

  typedef struct packed {
    logic [riscv_pkg::VADDR_W-1:0] vaddr;
    mem_cmd_t cmd;
  } tlb_req_t;

  typedef struct packed {
    logic miss;
    logic [riscv_pkg::PADDR_W-1:0] paddr;
  } tlb_resp_t;

  typedef struct packed {
    mem_cmd_t cmd;
    logic [riscv_pkg::PADDR_W-1:0] addr;
    logic [L2_CMD_TAG_W-1:0] tag;
    logic [ICACHE_DATA_W-1:0] data;
    logic [ICACHE_DATA_W/8-1:0] byte_en;
  } l2_req_t;

  typedef struct packed {
    logic [L2_CMD_TAG_W-1:0] tag;
    logic [ICACHE_DATA_W-1:0] data;
  } l2_resp_t;

  typedef struct packed {
    logic valid;
    logic [31:0] inst;
  } inst_buf_t;

  typedef enum {
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
    logic [31:0] inst;

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
  } sched_t;


  typedef struct packed {
    logic valid;
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


function issue_t assign_issue_t(sched_t in, logic rs1_hit, logic rs2_hit);
    issue_t ret;

    ret.valid = in.valid;
    ret.inst = in.inst;

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
  } release_t;

  typedef struct packed {
    logic valid;
    logic [msrh_pkg::RNID_W-1:0] rd_rnid;
    reg_t rd_type;
    logic [riscv_pkg::XLEN_W-1:0] rd_data;
  } target_t;

  typedef struct packed {
    logic                 valid;
    logic [CMT_BLK_W-1:0] cmt_id;
    logic [DISP_SIZE-1:0] grp_id;
    logic                 exc_vld;
  } done_rpt_t;

endpackage

`default_nettype wire
