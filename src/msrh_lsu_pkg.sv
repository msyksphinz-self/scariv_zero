package msrh_lsu_pkg;

  import msrh_pkg::*;

  localparam L2_CMD_TAG_W = 4;

  localparam L2_UPPER_TAG_IC  = 1'b0;
  localparam L2_UPPER_TAG_L1D = 1'b1;

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

  localparam LDQ_SIZE = 16;
  localparam STQ_SIZE = 16;
  localparam MEM_Q_SIZE = LDQ_SIZE > STQ_SIZE ? LDQ_SIZE : STQ_SIZE;


  typedef enum logic [ 1: 0] {
    LEN1B,
    LEN2B,
    LEN4B,
    LEN8B
  } size_t;

  typedef enum logic [ 2: 0] {
    NONE,
    L1D_CONFLICT,
    LRQ_ASSIGNED,
    LRQ_CONFLICT,
    LRQ_FULL
  } lmq_haz_t;

  typedef struct packed {
    logic valid;
    logic [riscv_pkg::VADDR_W-1:0] vaddr;
  } ic_req_t;

  typedef struct packed {
    logic valid;
    logic [riscv_pkg::VADDR_W-1:1]      addr;
    logic [ICACHE_DATA_W-1:0] data;
    logic [ICACHE_DATA_B_W-1:0] be;
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
  logic                           update;
  msrh_pkg::issue_t               inst;
  logic [msrh_pkg::LSU_INST_NUM-1: 0] pipe_sel_idx_oh;
  logic [msrh_pkg::CMT_BLK_W-1:0] cmt_id;
  logic [msrh_pkg::DISP_SIZE-1:0] grp_id;
  logic                           hazard_vld;
  logic [MEM_Q_SIZE-1:0]          index_oh;
  logic [riscv_pkg::VADDR_W-1: 0] vaddr;
} ex1_q_update_t;

typedef struct packed {
  logic          update;
  msrh_lsu_pkg::lmq_haz_t               hazard_typ;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_index_oh;
  logic [MEM_Q_SIZE-1:0]                index_oh;
} ex2_q_update_t;

// L1D interface
typedef struct packed {
  logic          valid;
  logic [riscv_pkg::PADDR_W-1: 0] addr;
  logic [msrh_lsu_pkg::DCACHE_DATA_W-1: 0] data;
} dc_update_t;

typedef struct packed {
  logic          valid;
  logic [riscv_pkg::PADDR_W-1: 0] paddr;
} dc_read_req_t;

typedef struct packed {
  logic            hit;
  logic            miss;
  logic            conflict;
  logic [msrh_lsu_pkg::DCACHE_DATA_W-1: 0] data;
} dc_read_resp_t;


// ---------
// STQ
// ---------
typedef enum logic[2:0] {
  INIT = 0,
  TLB_HAZ = 1,
  READY = 2,
  DONE = 3,
  COMMIT = 4
} stq_state_t;

typedef struct packed {
  logic          is_valid;
  logic [msrh_pkg::LSU_INST_NUM-1: 0]  pipe_sel_idx_oh;
  msrh_pkg::issue_t inst;
  logic [msrh_pkg::CMT_BLK_W-1:0] cmt_id;
  logic [msrh_pkg::DISP_SIZE-1:0] grp_id;
  msrh_lsu_pkg::stq_state_t state;
  logic [riscv_pkg::VADDR_W-1: 0] vaddr;
  logic [riscv_pkg::PADDR_W-1: 0] paddr;
  logic [riscv_pkg::XLEN_W-1: 0]  data;
} stq_entry_t;

typedef struct packed {
  logic          done;
  logic [msrh_pkg::CMT_BLK_W-1:0] cmt_id;
  logic [msrh_pkg::DISP_SIZE-1:0] grp_id;
} store_op_t;

typedef struct packed {
  logic [riscv_pkg::PADDR_W-1:0] paddr;
  size_t                         acc_size;
  logic [riscv_pkg::XLEN_W-1: 0] data;
} srq_req_t;

typedef struct packed {
  logic                          full;
  logic                          conflict;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_index_oh;
} srq_resp_t;


endpackage // msrh_lsu_pkg
