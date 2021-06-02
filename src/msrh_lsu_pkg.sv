package msrh_lsu_pkg;

  import msrh_pkg::*;

  localparam L2_CMD_TAG_W = 5;

  localparam L2_UPPER_TAG_IC  = 2'b00;
  localparam L2_UPPER_TAG_L1D = 2'b01;
  localparam L2_UPPER_TAG_PTW = 2'b10;

  localparam ICACHE_TAG_HIGH = riscv_pkg::XLEN_W;
  localparam ICACHE_TAG_LOW = 12;
  localparam ICACHE_WAY_W = 4;
  localparam ICACHE_DATA_B_W = msrh_conf_pkg::ICACHE_DATA_W / 8;


  localparam DCACHE_TAG_HIGH = riscv_pkg::XLEN_W;
  localparam DCACHE_TAG_LOW = 12;
  localparam DCACHE_WAY_W = 4;
  localparam DCACHE_DATA_B_W = msrh_conf_pkg::DCACHE_DATA_W / 8;

  localparam MEM_Q_SIZE = msrh_conf_pkg::LDQ_SIZE > msrh_conf_pkg::STQ_SIZE ?
                          msrh_conf_pkg::LDQ_SIZE :
                          msrh_conf_pkg::STQ_SIZE;

  // typedef enum logic [ 1: 0] {
  //   LEN1B,
  //   LEN2B,
  //   LEN4B,
  //   LEN8B
  // } size_t;

  typedef enum logic [ 2: 0] {
    NONE,
    L1D_CONFLICT,
    LRQ_ASSIGNED,
    LRQ_CONFLICT,
    LRQ_FULL,
    STQ_DEPEND
  } lmq_haz_t;

  typedef struct packed {
    logic valid;
    logic [riscv_pkg::VADDR_W-1:0] vaddr;
  } ic_req_t;

  typedef struct packed {
    logic valid;
    logic [riscv_pkg::VADDR_W-1:1]      addr;
    logic [msrh_conf_pkg::ICACHE_DATA_W-1:0] data;
    logic [ICACHE_DATA_B_W-1:0] be;
`ifdef SIMULATION
    logic [riscv_pkg::VADDR_W-1:0] addr_dbg;
`endif // SIMULATION
  } ic_resp_t;

  typedef enum logic [4:0] {
    M_XRD       = 5'b00000,  // int load
    M_XWR       = 5'b00001,  // int store
    M_PFR       = 5'b00010,  // prefetch with intent to read
    M_PFW       = 5'b00011,  // prefetch with intent to write
    M_XA_SWAP   = 5'b00100,
    M_FLUSH_ALL = 5'b00101,  // flush all lines
    M_XLR       = 5'b00110,
    M_XSC       = 5'b00111,
    M_XA_ADD    = 5'b01000,
    M_XA_XOR    = 5'b01001,
    M_XA_OR     = 5'b01010,
    M_XA_AND    = 5'b01011,
    M_XA_MIN    = 5'b01100,
    M_XA_MAX    = 5'b01101,
    M_XA_MINU   = 5'b01110,
    M_XA_MAXU   = 5'b01111,
    M_FLUSH     = 5'b10000,  // write back dirty data and cede R/W permissions
    M_PWR       = 5'b10001,  // partial (masked) store
    M_PRODUCE   = 5'b10010,  // write back dirty data and cede W permissions
    M_CLEAN     = 5'b10011,  // write back dirty data and retain R/W permissions
    M_SFENCE    = 5'b10100,  // flush TLB
    M_WOK       = 5'b10111   // check write permissions but don't perform a write
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
    logic          valid;
    logic [riscv_pkg::VADDR_W-1:0] vaddr;
    mem_cmd_t cmd;
    logic [$clog2(msrh_conf_pkg::DCACHE_DATA_W/8)-1: 0] size;
    logic                                               passthrough;
  } tlb_req_t;

  typedef struct packed {
    logic          ld;
    logic          st;
    logic          inst;
  } tlb_except_t;

  typedef struct packed {
    tlb_except_t       pf;
    tlb_except_t       ae;
    tlb_except_t       ma;
    logic              cacheable;
    logic              must_alloc;
    logic              prefetchable;
    logic              miss;
    logic [riscv_pkg::PADDR_W-1:0] paddr;
  } tlb_resp_t;

  typedef struct packed {
    mem_cmd_t cmd;
    logic [riscv_pkg::PADDR_W-1:0] addr;
    logic [L2_CMD_TAG_W-1:0] tag;
    logic [msrh_conf_pkg::ICACHE_DATA_W-1:0] data;
    logic [ICACHE_DATA_B_W-1:0] byte_en;
  } l2_req_t;

  typedef struct packed {
    logic [L2_CMD_TAG_W-1:0] tag;
    logic [msrh_conf_pkg::ICACHE_DATA_W-1:0] data;
  } l2_resp_t;

typedef struct packed {
  logic [riscv_pkg::PADDR_W-1:0] paddr;
} lrq_req_t;

typedef struct packed {
  logic                          full;
  logic                          conflict;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_index_oh;
} lrq_resp_t;

typedef struct packed {
  logic          valid;
  logic [riscv_pkg::PADDR_W-1:0] paddr;
  logic                           sent;
} lrq_entry_t;

typedef struct packed {
logic          valid;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] resolve_index_oh;
} lrq_resolve_t;

typedef struct packed {
  logic valid;
  logic rs1;
  logic rs2;
  logic [riscv_pkg::VADDR_W-1: 0] addr;
  // Temporary Disable
  // logic asid = UInt(width = asIdBits max 1) // TODO zero-width
} sfence_t;

typedef struct packed {
  logic          valid;
  logic [msrh_conf_pkg::STQ_SIZE-1: 0] resolve_index_oh;
} stq_resolve_t;

typedef struct packed {
  logic                           update;
  msrh_pkg::issue_t               inst;
  decoder_lsu_ctrl_pkg::size_t    size; // Memory Access Size
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] pipe_sel_idx_oh;
  logic [msrh_pkg::CMT_ID_W-1:0] cmt_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;
  logic                           hazard_valid;
  logic                           tlb_except_valid;
  msrh_pkg::except_t              tlb_except_type;
  logic [MEM_Q_SIZE-1:0]          index_oh;
  logic [riscv_pkg::VADDR_W-1: 0] vaddr;
  logic [riscv_pkg::PADDR_W-1: 0] paddr;
  logic                           st_data_valid;
  logic [riscv_pkg::XLEN_W-1: 0]  st_data;
} ex1_q_update_t;

typedef struct packed {
  logic          update;
  msrh_lsu_pkg::lmq_haz_t               hazard_typ;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_index_oh;
  logic [msrh_conf_pkg::STQ_SIZE-1: 0] stq_haz_idx;
  logic [MEM_Q_SIZE-1:0]                index_oh;
} ex2_q_update_t;

typedef struct packed {
  logic                                valid;
  logic [msrh_pkg::CMT_ID_W-1:0]      cmt_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;
  logic [riscv_pkg::PADDR_W-1: 3]      paddr;
  logic [ 7: 0]                        dw;
} ex2_addr_check_t;

// L1D interface
typedef struct packed {
  logic          valid;
  logic [riscv_pkg::PADDR_W-1: 0] addr;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] data;
  logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1: 0] be;
} dc_update_t;

typedef struct packed {
  logic          valid;
  logic [riscv_pkg::PADDR_W-1: 0] paddr;
} dc_read_req_t;

typedef struct packed {
  logic            hit;
  logic            miss;
  logic            conflict;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] data;
} dc_read_resp_t;

function logic [ 7: 0] gen_dw(decoder_lsu_ctrl_pkg::size_t size, logic [2:0] addr);
  case(size)
    decoder_lsu_ctrl_pkg::SIZE_DW : return 8'b1111_1111;
    decoder_lsu_ctrl_pkg::SIZE_W : begin
      if (addr[1:0] != 2'b00) $fatal(0, "gen_dw with SIZE_W, addr[1:0] should be zero");
      return 8'b0000_1111 << addr;
    end
    decoder_lsu_ctrl_pkg::SIZE_H  : begin
      if (addr[0] != 1'b0) $fatal(0, "gen_dw with SIZE_H, addr[0] should be zero");
      return 8'b0000_0011 << addr;
    end
    decoder_lsu_ctrl_pkg::SIZE_B  : return 8'b0000_0001 << addr;
    default : return 'h0;
  endcase // case (size)
endfunction // gen_dw


// addr1/size1 includes addr2_dw ?
function logic is_dw_included(decoder_lsu_ctrl_pkg::size_t size1, logic [2:0] addr1,
                              logic [7:0] addr2_dw);
  logic [ 7: 0] addr1_dw;
  addr1_dw = gen_dw(size1, addr1);

  return (addr1_dw & addr2_dw) == addr2_dw;
endfunction // is_dw_included

// ---------
// STQ
// ---------
typedef enum logic[3:0] {
  STQ_INIT = 0,
  STQ_TLB_HAZ = 1,
  STQ_READY = 2,
  STQ_DONE_EX2 = 3,
  STQ_COMMIT = 4,
  STQ_WAIT_ST_DATA = 5,
  STQ_WAIT_LRQ_REFILL = 6,
  STQ_COMMIT_L1D_CHECK = 7,
  STQ_L1D_UPDATE = 8,
  STQ_DEAD = 9,
  STQ_WAIT_COMMIT = 10,
  STQ_DONE_EX3 = 11
} stq_state_t;

typedef struct packed {
  logic          is_valid;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  pipe_sel_idx_oh;
  msrh_pkg::issue_t inst;
  decoder_lsu_ctrl_pkg::size_t    size; // Memory Access Size
  logic [msrh_pkg::CMT_ID_W-1:0] cmt_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;
  stq_state_t                     state;
  logic [riscv_pkg::VADDR_W-1: 0] vaddr;
  logic [riscv_pkg::PADDR_W-1: 0] paddr;
  logic                           paddr_valid;
  logic [riscv_pkg::XLEN_W-1: 0]  rs2_data;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_index_oh;

  logic                                 except_valid;
  msrh_pkg::except_t                    except_type;
} stq_entry_t;


typedef struct packed {
  logic          done;
  logic [msrh_pkg::CMT_ID_W-1:0] cmt_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;
} store_op_t;

typedef struct packed {
  logic [riscv_pkg::PADDR_W-1:0] paddr;
  decoder_lsu_ctrl_pkg::size_t   acc_size;
  logic [riscv_pkg::XLEN_W-1: 0] data;
} srq_req_t;

typedef struct packed {
  logic                          full;
  logic                          conflict;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_index_oh;
} srq_resp_t;

function logic is_amo_logical(mem_cmd_t cmd);
  return cmd == M_XA_SWAP ||
         cmd == M_XA_XOR  ||
         cmd == M_XA_OR   ||
         cmd == M_XA_AND;
endfunction // isAMOLogical
function logic is_amo_arithmetic(mem_cmd_t cmd);
  return cmd == M_XA_ADD  ||
         cmd == M_XA_MIN  ||
         cmd == M_XA_MAX  ||
         cmd == M_XA_MINU ||
         cmd == M_XA_MAXU;
endfunction // isAMOLogical
function logic is_amo(mem_cmd_t cmd);
  return is_amo_logical(cmd) | is_amo_arithmetic(cmd);
endfunction // isAMOLogical
function logic is_prefetch(mem_cmd_t cmd);
  return cmd == M_PFR ||
         cmd == M_PFW;
endfunction // isAMOLogical
function logic is_read(mem_cmd_t cmd);
  return  cmd == M_XRD ||
          cmd == M_XLR ||
          cmd == M_XSC ||
          is_amo(cmd);
endfunction // isAMOLogical
function logic is_write(mem_cmd_t cmd);
  return cmd == M_XWR ||
         cmd == M_PWR ||
         cmd == M_XSC ||
         is_amo(cmd);
endfunction // isAMOLogical
function logic is_write_intent(mem_cmd_t cmd);
  return is_write(cmd) ||
         cmd == M_PFW  ||
         cmd=== M_XLR;
endfunction // isAMOLogical

// ---------
// LDQ
// ---------

typedef enum logic[3:0] {
  LDQ_INIT = 0,
  LDQ_EX2_RUN = 1,
  LDQ_LRQ_HAZ = 2,
  LDQ_STQ_HAZ = 3,
  LDQ_TLB_HAZ = 4,
  LDQ_READY = 5,
  LDQ_CHECK_ST_DEPEND = 6,
  LDQ_EX3_DONE = 7,
  LDQ_DEAD = 8,
  LDQ_WAIT_COMPLETE = 9,
  LDQ_EXCEPT = 10
} ldq_state_t;

typedef struct packed {
  logic          is_valid;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  pipe_sel_idx_oh;
  msrh_pkg::issue_t               inst;
  decoder_lsu_ctrl_pkg::size_t    size; // Memory Access Size
  logic [msrh_pkg::CMT_ID_W-1:0] cmt_id;
  logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;
  ldq_state_t                     state;
  logic [riscv_pkg::VADDR_W-1: 0] vaddr;
  logic [riscv_pkg::PADDR_W-1: 0] paddr;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_haz_index_oh;
  logic [msrh_conf_pkg::STQ_SIZE-1: 0]  stq_haz_idx;

  logic                                 except_valid;
  msrh_pkg::except_t                    except_type;
} ldq_entry_t;

// -----
// TLB
// -----

localparam PG_IDX_W = 12;
localparam VPN_W = riscv_pkg::VADDR_W - PG_IDX_W;
localparam VPN_FIELD_W = 10 - $clog2(riscv_pkg::XLEN_W / 32);
localparam SECTOR_NUM = 4;


typedef struct packed {
  logic [riscv_pkg::PPN_W-1: 0] ppn;
  logic [ 1: 0]                 reserved_for_software;
  logic                         d;
  logic                         a;
  logic                         g;
  logic                         u;
  logic                         x;
  logic                         w;
  logic                         r;
  logic                         v;
} pte_t;

typedef struct packed {
  logic              valid;
  logic [VPN_W-1: 0] addr;
} ptw_req_t;

typedef struct packed {
  logic          valid;
  logic                          ae;
  pte_t                          pte;
  logic [$clog2(riscv_pkg::PG_LEVELS)-1: 0] level;
  logic                          fragmented_superpage;
  logic                          homogeneous;
} ptw_resp_t;

typedef struct packed {
  logic  dummy;
} pmp_t;

// LSU Access Interface Status

typedef enum logic [2:0]{
  STATUS_NONE = 0,
  STATUS_HIT = 1,
  STATUS_MISS = 2,
  STATUS_L1D_CONFLICT = 3,
  STATUS_LRQ_CONFLICT = 4
} lsu_status_t;

endpackage // msrh_lsu_pkg
