package msrh_lsu_pkg;

  import msrh_pkg::*;

  localparam L2_CMD_TAG_W = 5;

  localparam L2_UPPER_TAG_IC     = 2'b00;
  localparam L2_UPPER_TAG_RD_L1D = 2'b01;
  localparam L2_UPPER_TAG_WR_L1D = 2'b10;
  localparam L2_UPPER_TAG_PTW    = 2'b11;

  localparam ICACHE_TAG_HIGH = riscv_pkg::XLEN_W;
  localparam ICACHE_TAG_LOW = $clog2(msrh_conf_pkg::ICACHE_WORDS);
  localparam ICACHE_DATA_B_W = msrh_conf_pkg::ICACHE_DATA_W / 8;


  localparam DCACHE_DATA_B_W = msrh_conf_pkg::DCACHE_DATA_W / 8;

  localparam DCACHE_TAG_HIGH = riscv_pkg::PADDR_W-1;
  localparam DCACHE_TAG_LOW = $clog2(DCACHE_DATA_B_W * msrh_conf_pkg::DCACHE_WORDS);

localparam DCACHE_BANK_LOW  = $clog2(DCACHE_DATA_B_W);
localparam DCACHE_BANK_HIGH = $clog2(msrh_conf_pkg::DCACHE_BANKS) + DCACHE_BANK_LOW - 1;

  localparam MEM_Q_SIZE = msrh_conf_pkg::LDQ_SIZE > msrh_conf_pkg::STQ_SIZE ?
                          msrh_conf_pkg::LDQ_SIZE :
                          msrh_conf_pkg::STQ_SIZE;

    typedef enum logic [ 1: 0] {
        MESI_INVALID = 0,
        MESI_EXCLUSIVE = 1,
        MESI_SHARED = 2,
        MESI_MODIFIED = 3
    } mesi_t;

typedef struct   packed {
  logic          r;
  logic          w;
  logic          x;
  logic          a;
  logic          c;
} map_attr_t;

  typedef enum logic [ 2: 0] {
    NONE,
    L1D_CONFLICT,
    LRQ_ASSIGNED,
    LRQ_CONFLICT,
    LRQ_FULL,
    LRQ_EVICT_CONFLICT
  } lmq_haz_t;

  typedef struct packed {
    logic valid;
    msrh_pkg::vaddr_t vaddr;
  } ic_req_t;

  typedef struct packed {
    logic valid;
    logic [riscv_pkg::VADDR_W-1:1]      vaddr;
    logic [msrh_conf_pkg::ICACHE_DATA_W-1:0] data;
    logic [ICACHE_DATA_B_W-1:0] be;
`ifdef SIMULATION
    msrh_pkg::vaddr_t vaddr_dbg;
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
    msrh_pkg::vaddr_t vaddr;
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
    msrh_pkg::paddr_t paddr;
  } tlb_resp_t;

  typedef struct packed {
    mem_cmd_t cmd;
    msrh_pkg::paddr_t addr;
    logic [L2_CMD_TAG_W-1:0] tag;
    logic [msrh_conf_pkg::ICACHE_DATA_W-1:0] data;
    logic [ICACHE_DATA_B_W-1:0] byte_en;
  } l2_req_t;

  typedef struct packed {
    logic [L2_CMD_TAG_W-1:0] tag;
    logic [msrh_conf_pkg::ICACHE_DATA_W-1:0] data;
  } l2_resp_t;

typedef struct packed {
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] data;
  logic [$clog2(msrh_conf_pkg::DCACHE_WAYS)-1: 0] way;
  msrh_pkg::paddr_t           paddr;
} evict_payload_t;

typedef struct packed {
  msrh_pkg::paddr_t paddr;
  logic   evict_valid;
  evict_payload_t evict_payload;
} lrq_req_t;

typedef struct packed {
  logic                          full;
  logic                          evict_conflict;
  logic                          conflict;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_index_oh;
} lrq_resp_t;

typedef struct packed {
  logic          valid;
  msrh_pkg::paddr_t paddr;
  logic                          sent;
  logic                          get_data;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1:0] data;
  logic [$clog2(msrh_conf_pkg::DCACHE_WAYS)-1: 0] way;
} miss_entry_t;

function miss_entry_t assign_miss_entry (logic valid, lrq_req_t req);
  miss_entry_t ret;

  ret = 'h0;

  ret.valid = valid;
  ret.paddr = {req.paddr[riscv_pkg::PADDR_W-1:$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W)],
               {$clog2(msrh_lsu_pkg::DCACHE_DATA_B_W){1'b0}}};
  ret.way = req.evict_payload.way;

  return ret;

endfunction // assign_lrq_entry

typedef struct packed {
  logic                                      valid;
  msrh_pkg::alen_t             data;
  logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1: 0] be;
} evict_merge_t;

typedef struct packed {
  logic          valid;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] resolve_index_oh;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_entry_valids;
} lrq_resolve_t;

typedef struct packed {
  logic valid;
  logic rs1;
  logic rs2;
  msrh_pkg::vaddr_t addr;
  // Temporary Disable
  // logic asid = UInt(width = asIdBits max 1) // TODO zero-width
} sfence_t;

typedef struct packed {
  logic                           update;
  // msrh_pkg::issue_t               inst;
  decoder_lsu_ctrl_pkg::size_t    size; // Memory Access Size
  // logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] pipe_sel_idx_oh;
  msrh_pkg::cmt_id_t cmt_id;
  msrh_pkg::grp_id_t grp_id;
  logic                           hazard_valid;
  logic                           tlb_except_valid;
  msrh_pkg::except_t              tlb_except_type;
  logic [MEM_Q_SIZE-1:0]          index_oh;
  msrh_pkg::vaddr_t vaddr;
  msrh_pkg::paddr_t paddr;
  logic                           st_data_valid;
  msrh_pkg::alen_t  st_data;
} ex1_q_update_t;

typedef struct packed {
  logic          update;
  lmq_haz_t               hazard_typ;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_index_oh;
  logic [MEM_Q_SIZE-1:0]                index_oh;
} ex2_q_update_t;

typedef struct packed {
  logic                                valid;
  msrh_pkg::cmt_id_t      cmt_id;
  msrh_pkg::grp_id_t grp_id;
  logic [riscv_pkg::PADDR_W-1: 3]      paddr;
  logic [ 7: 0]                        dw;
} ex2_addr_check_t;

// L1D interface
typedef struct packed {
  logic                                           s0_valid;
  logic                                           s0_tag_update_valid;
  logic [$clog2(msrh_conf_pkg::DCACHE_WAYS)-1: 0] s0_way;
  msrh_pkg::paddr_t                 s0_paddr;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0]       s0_data;
  logic [DCACHE_DATA_B_W-1: 0]                    s0_be;
} dc_wr_req_t;

typedef struct packed {
  logic                                     s1_hit;
  logic                                     s1_miss;
  logic                                     s2_evicted_valid;
  msrh_pkg::paddr_t           s2_evicted_paddr;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] s2_evicted_data;
} dc_wr_resp_t;

typedef struct packed {
  msrh_pkg::paddr_t                  s0_paddr;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1:0]        s0_data;
  logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1:0]       s0_be;
  logic [$clog2(msrh_conf_pkg::DCACHE_WAYS)-1: 0] s0_way;
} s0_l1d_wr_req_t;


typedef struct packed {
  logic                                           s1_hit;
  logic                                           s1_miss;
  logic                                           s1_conflict;
} s1_l1d_wr_resp_t;


typedef struct packed {
  logic                                           s2_evicted_valid;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0]       s2_evicted_data;
  msrh_pkg::paddr_t                 s2_evicted_paddr;
} s2_l1d_wr_resp_t;


typedef struct packed {
  logic          valid;
  logic          h_pri;
  msrh_pkg::paddr_t paddr;
} dc_read_req_t;

typedef struct packed {
  logic            hit;
  logic [$clog2(msrh_conf_pkg::DCACHE_WAYS)-1: 0] hit_way;
  logic            miss;
  logic            conflict;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] data;

  // Eviction: Replaced Address
  logic                                    replace_valid;
  logic [$clog2(msrh_conf_pkg::DCACHE_WAYS)-1: 0]  replace_way;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] replace_data;
  msrh_pkg::paddr_t          replace_paddr;

} dc_read_resp_t;

function automatic logic [msrh_pkg::ALEN_W/8 + msrh_pkg::ALEN_W-1: 0]
  fwd_align (decoder_lsu_ctrl_pkg::size_t size, msrh_pkg::alenb_t fwd_dw, msrh_pkg::alen_t fwd_data,
             logic [$clog2(msrh_pkg::ALEN_W/8)-1:0] paddr);

  msrh_pkg::alenb_t                  w_aligned_fwd_dw;
  msrh_pkg::alen_t                  w_aligned_fwd_data;

  case (size)
    decoder_lsu_ctrl_pkg::SIZE_DW : begin
      w_aligned_fwd_dw   = fwd_dw;
      w_aligned_fwd_data = fwd_data;
    end
    decoder_lsu_ctrl_pkg::SIZE_W  : begin
// `ifdef RV32
//       w_aligned_fwd_dw   = fwd_dw;
//       w_aligned_fwd_data = fwd_data;
// `else // RV32
      w_aligned_fwd_dw   = fwd_dw   >> {paddr[$clog2(msrh_pkg::ALEN_W/8)-1], 2'b00};
      w_aligned_fwd_data = fwd_data >> {paddr[$clog2(msrh_pkg::ALEN_W/8)-1], 2'b00, 3'b000};
// `endif // RV32
    end
    decoder_lsu_ctrl_pkg::SIZE_H  : begin
      w_aligned_fwd_dw   = fwd_dw   >> {paddr[$clog2(msrh_pkg::ALEN_W/8)-1:1], 1'b0};
      w_aligned_fwd_data = fwd_data >> {paddr[$clog2(msrh_pkg::ALEN_W/8)-1:1], 1'b0, 3'b000};
    end
    decoder_lsu_ctrl_pkg::SIZE_B  : begin
      w_aligned_fwd_dw   = fwd_dw   >>  paddr[$clog2(msrh_pkg::ALEN_W/8)-1:0];
      w_aligned_fwd_data = fwd_data >> {paddr[$clog2(msrh_pkg::ALEN_W/8)-1:0], 3'b000};
    end
    default : begin
      w_aligned_fwd_dw   = 'h0;
      w_aligned_fwd_data = 'h0;
    end
  endcase // case (r_ex2_pipe_ctrl.size)

  return {w_aligned_fwd_dw, w_aligned_fwd_data};

endfunction // fwd_align


function msrh_pkg::alenb_t gen_dw(decoder_lsu_ctrl_pkg::size_t size, logic [$clog2(msrh_pkg::ALEN_W/8)-1:0] addr);
  case(size)
    decoder_lsu_ctrl_pkg::SIZE_DW : return 8'b1111_1111;
    decoder_lsu_ctrl_pkg::SIZE_W : begin
      // if (addr[1:0] != 2'b00) $fatal(0, "gen_dw with SIZE_W, addr[1:0] should be zero");
      /* verilator lint_off WIDTH */
      return 8'b0000_1111 << addr;
    end
    decoder_lsu_ctrl_pkg::SIZE_H  : begin
      // if (addr[0] != 1'b0) $fatal(0, "gen_dw with SIZE_H, addr[0] should be zero");
      /* verilator lint_off WIDTH */
      return 8'b0000_0011 << addr;
    end
    decoder_lsu_ctrl_pkg::SIZE_B  : begin
      /* verilator lint_off WIDTH */
      return 8'b0000_0001 << addr;
    end
    default : return 'h0;
  endcase // case (size)
endfunction // gen_dw


// addr1/size1 includes addr2_dw ?
function logic is_dw_included(decoder_lsu_ctrl_pkg::size_t size1, logic [$clog2(msrh_pkg::ALEN_W/8)-1:0] addr1,
                              logic [msrh_pkg::ALEN_W/8-1:0] addr2_dw);
  msrh_pkg::alenb_t addr1_dw;
  addr1_dw = gen_dw(size1, addr1);

  return (addr1_dw & addr2_dw) == addr2_dw;
endfunction // is_dw_included


function logic [DCACHE_DATA_B_W-1: 0] gen_dw_cacheline(decoder_lsu_ctrl_pkg::size_t size,
                                                       logic [$clog2(DCACHE_DATA_B_W)-1:0] addr);
  case(size)
    decoder_lsu_ctrl_pkg::SIZE_DW : return 'hff << addr;
    decoder_lsu_ctrl_pkg::SIZE_W  : return 'h0f << addr;
    decoder_lsu_ctrl_pkg::SIZE_H  : return 'h03 << addr;
    decoder_lsu_ctrl_pkg::SIZE_B  : return 'h01 << addr;
    default : return 'h0;
  endcase // case (size)
endfunction // gen_dw


// ---------
// STQ
// ---------
typedef enum logic[3:0] {
  STQ_INIT = 0,
  STQ_TLB_HAZ = 1,
  STQ_ISSUE_WAIT = 2,
  STQ_DONE_EX2 = 3,
  STQ_COMMIT = 4,
  STQ_WAIT_ST_DATA = 5,
  STQ_DEAD = 9,
  STQ_WAIT_COMMIT = 10,
  STQ_DONE_EX3 = 11,
  STQ_ISSUED = 12
} stq_state_t;

typedef struct packed {
  logic           is_valid;
  brtag_t          brtag;
  brmask_t         br_mask;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  pipe_sel_idx_oh;
  msrh_pkg::issue_t inst;
  decoder_lsu_ctrl_pkg::size_t    size; // Memory Access Size
  msrh_pkg::cmt_id_t cmt_id;
  msrh_pkg::grp_id_t grp_id;
  stq_state_t        state;
  msrh_pkg::vaddr_t  vaddr;
  msrh_pkg::paddr_t  paddr;
  logic                                  paddr_valid;
  logic                                  is_rs2_get;
  msrh_pkg::alen_t                       rs2_data;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_index_oh;

  logic              except_valid;
  msrh_pkg::except_t except_type;

  logic              another_flush_valid;
  msrh_pkg::cmt_id_t another_flush_cmt_id;
  msrh_pkg::grp_id_t another_flush_grp_id;

`ifdef SIMULATION
    logic [63: 0]                     kanata_id;
`endif // SIMULATION
} stq_entry_t;


typedef struct packed {
  logic          done;
  msrh_pkg::cmt_id_t cmt_id;
  msrh_pkg::grp_id_t grp_id;
} store_op_t;

typedef struct packed {
  msrh_pkg::paddr_t paddr;
  decoder_lsu_ctrl_pkg::size_t   acc_size;
  msrh_pkg::alen_t data;
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
  LDQ_LRQ_CONFLICT = 2,
  LDQ_TLB_HAZ = 4,
  LDQ_ISSUE_WAIT = 5,
  LDQ_CHECK_ST_DEPEND = 6,
  LDQ_EX3_DONE = 7,
  LDQ_WAIT_COMMIT = 8,
  LDQ_WAIT_ENTRY_CLR = 9,
  LDQ_ISSUED = 10,
  LDQ_LRQ_EVICT_HAZ = 11,
  LDQ_LRQ_FULL = 12
} ldq_state_t;

typedef struct packed {
  logic          is_valid;
  brtag_t brtag;
  brmask_t         br_mask;
  logic [msrh_conf_pkg::LSU_INST_NUM-1: 0]  pipe_sel_idx_oh;
  msrh_pkg::issue_t               inst;
  decoder_lsu_ctrl_pkg::size_t    size; // Memory Access Size
  msrh_pkg::cmt_id_t cmt_id;
  msrh_pkg::grp_id_t grp_id;
  ldq_state_t                     state;
  logic                           is_get_data;
  msrh_pkg::vaddr_t vaddr;
  msrh_pkg::paddr_t paddr;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_haz_index_oh;

  logic                                 except_valid;
  msrh_pkg::except_t                    except_type;

`ifdef SIMULATION
    logic [63: 0]                     kanata_id;
`endif // SIMULATION

} ldq_entry_t;

// -----
// TLB
// -----

localparam PG_IDX_W = 12;
localparam VPN_W = riscv_pkg::VADDR_MSB - PG_IDX_W + 1;
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


// Snoop interface

typedef struct packed {
  msrh_pkg::paddr_t paddr;
} snoop_req_t;

typedef struct packed {
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] data;
  logic [DCACHE_DATA_B_W-1: 0] be;
} snoop_resp_t;


// -----------------------
// Store Buffer Interface
// -----------------------
localparam ST_BUF_WIDTH = (msrh_pkg::ALEN_W * 2);
localparam ST_BUF_ENTRY_SIZE = msrh_conf_pkg::STQ_SIZE / 4;

typedef enum logic [1:0] {
  ST_BUF_ALLOC = 0,
  ST_BUF_MERGE = 1,
  ST_BUF_FULL  = 2
} st_buffer_resp_t;

typedef struct packed {
  logic                                                valid;
  logic [riscv_pkg::PADDR_W-1: $clog2(ST_BUF_WIDTH/8)] paddr;
  logic [ST_BUF_WIDTH/8-1:0]                           strb;
  logic [ST_BUF_WIDTH-1: 0]                            data;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0]                lrq_index_oh;
`ifdef SIMULATION
  msrh_pkg::cmt_id_t cmt_id;
  msrh_pkg::grp_id_t grp_id;
`endif // SIMULATION
} st_buffer_entry_t;

typedef enum logic [ 3: 0] {
  ST_BUF_INIT         = 0,
  ST_BUF_RD_L1D       = 1,
  ST_BUF_RESP_L1D     = 2,
  ST_BUF_L1D_UPDATE   = 3,
  ST_BUF_L1D_UPD_RESP = 4,
  ST_BUF_LRQ_REFILL   = 5,
  ST_BUF_WAIT_REFILL  = 6,
  ST_BUF_WAIT_FULL    = 7,
  ST_BUF_WAIT_EVICT   = 8,
  ST_BUF_L1D_MERGE    = 9,
  ST_BUF_L1D_MERGE2   = 10,
  ST_BUF_WAIT_FINISH  = 11
} st_buffer_state_t;

function st_buffer_entry_t assign_st_buffer (msrh_pkg::cmt_id_t cmt_id,
                                             msrh_pkg::grp_id_t grp_id,
                                             msrh_pkg::paddr_t  paddr,
                                             logic [ST_BUF_WIDTH/8-1: 0] strb,
                                             logic [ST_BUF_WIDTH-1: 0]   data
                                             );
  st_buffer_entry_t ret;

  ret = 'h0;

  ret.valid = 1'b1;
  ret.paddr = paddr[riscv_pkg::PADDR_W-1:$clog2(ST_BUF_WIDTH/8)];
  ret.strb  = strb;
  ret.data  = data;

`ifdef SIMULATION
  ret.cmt_id = cmt_id;
  ret.grp_id = grp_id;
`endif // SIMULATION

  return ret;
endfunction // assign_st_buffer


endpackage // msrh_lsu_pkg
