// ------------------------------------------------------------------------
// NAME : scariv_lsu_pkg
// TYPE : package
// ------------------------------------------------------------------------
// LSU Package
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

package scariv_lsu_pkg;
  import scariv_pkg::*;
  import decoder_inst_cat_pkg::*;

  localparam L2_CMD_TAG_W = 7;

  localparam L2_UPPER_TAG_IC     = 2'b00;
  localparam L2_UPPER_TAG_RD_L1D = 2'b01;
  localparam L2_UPPER_TAG_WR_L1D = 2'b10;
  localparam L2_UPPER_TAG_PTW    = 2'b11;

  localparam ICACHE_TAG_HIGH = riscv_pkg::XLEN_W;
  localparam ICACHE_TAG_LOW = $clog2(scariv_conf_pkg::ICACHE_WORDS);
  localparam ICACHE_DATA_B_W = scariv_conf_pkg::ICACHE_DATA_W / 8;

  localparam DCACHE_DATA_B_W = scariv_conf_pkg::DCACHE_DATA_W / 8;

  localparam DCACHE_TAG_HIGH = riscv_pkg::PADDR_W-1;
  localparam DCACHE_TAG_LOW  = $clog2(DCACHE_DATA_B_W * scariv_conf_pkg::DCACHE_WORDS) < 12 ? $clog2(DCACHE_DATA_B_W * scariv_conf_pkg::DCACHE_WORDS) : 12;

localparam DCACHE_BANK_LOW  = $clog2(DCACHE_DATA_B_W);
localparam DCACHE_BANK_HIGH = $clog2(scariv_conf_pkg::DCACHE_BANKS) + DCACHE_BANK_LOW - 1;

// ---------------------------
// L1D Cache Port declaration
// ---------------------------
// LSU Pipeline + STQ Interface + PTW + Snoop
localparam L1D_LS_PORT_BASE  = 0;

localparam L1D_SNOOP_PORT    = 0;
localparam L1D_PTW_PORT      = L1D_SNOOP_PORT + 1;
localparam L1D_MISSU_PORT    = L1D_PTW_PORT   + 1;
localparam L1D_ST_RD_PORT    = L1D_MISSU_PORT + 1;
localparam L1D_PIPT_PORT_NUM = L1D_ST_RD_PORT + 1;



//         standard                                   (512 / 8) *                           128 *                            4 = 32,768 B (8KB)
//         boomv3                                     (128 / 8) *                            64 *                            4 = 4096 B (4KB)
localparam DCACHE_B_SIZE     = (DCACHE_DATA_B_W) * scariv_conf_pkg::DCACHE_WORDS * scariv_conf_pkg::DCACHE_WAYS;
localparam DCACHE_ACC_LENGTH = $clog2((DCACHE_DATA_B_W) * scariv_conf_pkg::DCACHE_WORDS);
localparam DCACHE_COLOR_W    = DCACHE_ACC_LENGTH > 12 ? DCACHE_ACC_LENGTH - 12 : 0;
typedef logic [DCACHE_COLOR_W-1: 0] dc_color_t;
typedef logic [DCACHE_ACC_LENGTH-1: $clog2(DCACHE_DATA_B_W)] dc_index_t;

function automatic dc_index_t gen_dc_index (scariv_pkg::vaddr_t va);
  return va[DCACHE_ACC_LENGTH-1: $clog2(scariv_conf_pkg::DCACHE_DATA_W/8)];
endfunction // gen_dc_index

function automatic dc_index_t gen_dc_pa_index (scariv_pkg::paddr_t pa, dc_color_t color);
  if (DCACHE_ACC_LENGTH > 12) begin
    return {color, pa[11: $clog2(DCACHE_DATA_B_W)]};
  end else begin
    return pa[DCACHE_ACC_LENGTH-1: $clog2(DCACHE_DATA_B_W)];
  end
endfunction // gen_dc_pa_index

// DCache Data Types
typedef logic [$clog2(scariv_conf_pkg::DCACHE_WAYS)-1: 0] dc_ways_idx_t;
typedef logic [scariv_conf_pkg::DCACHE_WAYS-1 : 0]        dc_ways_t;
typedef logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]       dc_data_t;
typedef logic [scariv_conf_pkg::DCACHE_DATA_W/8-1: 0]     dc_strb_t;

localparam MEM_Q_SIZE = scariv_conf_pkg::LDQ_SIZE > scariv_conf_pkg::STQ_SIZE ?
                        scariv_conf_pkg::LDQ_SIZE :
                        scariv_conf_pkg::STQ_SIZE;

localparam LSU_IQ_ENTRY_SIZE = scariv_conf_pkg::MEM_DISP_SIZE / scariv_conf_pkg::LSU_INST_NUM;

localparam HAZARD_INDEX_SIZE = scariv_conf_pkg::MSHR_ENTRY_SIZE > scariv_conf_pkg::STQ_SIZE ?
                               scariv_conf_pkg::MSHR_ENTRY_SIZE :
                               scariv_conf_pkg::STQ_SIZE;

typedef enum logic [ 1: 0] {
  MESI_INVALID   = 0,
  MESI_EXCLUSIVE = 1,
  MESI_SHARED    = 2,
  MESI_MODIFIED  = 3
} mesi_t;

typedef struct   packed {
  logic          r;
  logic          w;
  logic          x;
  logic          a;
  logic          c;
} map_attr_t;

typedef enum logic [ 2: 0] {
  EX1_HAZ_NONE,
  EX1_HAZ_TLB_MISS,
  EX1_HAZ_UC_ACCESS
} ex1_haz_t;


typedef enum logic [ 2: 0] {
  EX2_HAZ_NONE,
  EX2_HAZ_L1D_CONFLICT,
  EX2_HAZ_MSHR_ASSIGNED,
  EX2_HAZ_MSHR_FULL,
  EX2_HAZ_OLDER_SAME_ADDR,
  EX2_HAZ_RMW_ORDER_HAZ,
  EX2_HAZ_STQ_NONFWD_HAZ,
  EX2_HAZ_STQ_FWD_MISS   // Only use in COARSE_LDST_FWD mode
} ex2_haz_t;

  typedef enum logic [ 2: 0] { LSU_SCHED_INIT, LSU_SCHED_WAIT, LSU_SCHED_ISSUED, LSU_SCHED_HAZ_WAIT,
                                LSU_SCHED_CLEAR } lsu_sched_state_t;

  typedef enum logic {
    LSU_ISSUE_HAZ_TLB_MISS,
    LSU_ISSUE_HAZ_UC_ACCESS
  } lsu_issue_haz_reason_t;


typedef struct packed {
  decoder_inst_cat_pkg::inst_cat_t cat;
  logic [31: 0]                    inst;
  scariv_pkg::reg_wr_issue_t       wr_reg;
`ifdef SIMULATION
  scariv_pkg::vaddr_t sim_pc_addr;
  logic               sim_is_rvc;
  logic [63: 0]       kanata_id;
`endif // SIMULATION
} iq_payload_t;

typedef struct packed {
  logic   valid;

  cmt_id_t cmt_id;
  grp_id_t grp_id;

  logic need_oldest;
  logic oldest_valid;

  lsu_issue_haz_reason_t  haz_reason;

  reg_rd_issue_t [ 0: 0] rd_regs;
} iq_entry_t;

typedef struct packed {
  logic   valid;
  logic [31:0] inst;
  inst_cat_t   cat;
  brtag_t      brtag;

  cmt_id_t cmt_id;
  grp_id_t grp_id;

  logic                   need_oldest;
  logic                   oldest_valid;

  lsu_issue_haz_reason_t  haz_reason;

  reg_wr_issue_t         wr_reg;
  reg_rd_issue_t [ 0: 0] rd_regs;

`ifdef SIMULATION
  logic         sim_is_rvc;
  vaddr_t       sim_pc_addr;
  logic [63: 0] kanata_id;
`endif // SIMULATION
} lsu_issue_entry_t;


function iq_entry_t assign_entry (disp_t in, logic flush,
                                  cmt_id_t cmt_id,
                                  grp_id_t grp_id,
                                  logic [ 1: 0] rs_rel_hit, logic [ 1: 0] rs_phy_hit, logic [ 1: 0] rs_may_mispred, scariv_pkg::rel_bus_idx_t[ 1: 0] rs_rel_index,
                                  logic stq_rmw_existed, logic oldest_valid);
  iq_entry_t ret;
  ret.valid = in.valid;
  ret.cmt_id = cmt_id;
  ret.grp_id = grp_id;

  ret.need_oldest      = stq_rmw_existed | oldest_valid;
  ret.oldest_valid     = 1'b0;

  for (int rs_idx = 0; rs_idx < 1; rs_idx++) begin
    ret.rd_regs[rs_idx].valid         = in.rd_regs[rs_idx].valid;
    ret.rd_regs[rs_idx].typ           = in.rd_regs[rs_idx].typ;
    ret.rd_regs[rs_idx].regidx        = in.rd_regs[rs_idx].regidx;
    ret.rd_regs[rs_idx].rnid          = in.rd_regs[rs_idx].rnid;
    ret.rd_regs[rs_idx].ready         = in.rd_regs[rs_idx].ready | rs_rel_hit[rs_idx] & ~rs_may_mispred[rs_idx] | rs_phy_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready[0] = rs_rel_hit[rs_idx];
    ret.rd_regs[rs_idx].predict_ready[1] = 1'b0;
    if (ret.rd_regs[rs_idx].predict_ready[0]) begin
      ret.rd_regs[rs_idx].early_index = rs_rel_index[rs_idx];
    end
  end

  return ret;

endfunction  // assign_issue_t


function automatic iq_payload_t assign_payload (scariv_pkg::disp_t in);
  iq_payload_t ret;
  ret.cat       = in.cat    ;
  ret.inst      = in.inst   ;
  ret.wr_reg.valid  = in.wr_reg.valid ;
  ret.wr_reg.typ    = in.wr_reg.typ   ;
  ret.wr_reg.regidx = in.wr_reg.regidx;
  ret.wr_reg.rnid   = in.wr_reg.rnid  ;

`ifdef SIMULATION
  ret.sim_pc_addr = in.pc_addr;
  ret.sim_is_rvc  = in.rvc_inst_valid;
  ret.kanata_id   = in.kanata_id;
`endif // SIMULATION

  return ret;
endfunction // assign_payload

function automatic lsu_issue_entry_t assign_issue (iq_entry_t iq, iq_payload_t payload);
  lsu_issue_entry_t ret;
  ret.valid   = iq.valid     ;

  ret.cmt_id  = iq.cmt_id    ;
  ret.grp_id  = iq.grp_id    ;

  ret.wr_reg  = payload.wr_reg;
  ret.rd_regs = iq.rd_regs    ;

  ret.need_oldest   = iq.need_oldest;
  ret.oldest_valid  = iq.oldest_valid;

  ret.cat     = payload.cat       ;
  ret.inst    = payload.inst      ;
`ifdef SIMULATION
  ret.sim_pc_addr = payload.sim_pc_addr;
  ret.sim_is_rvc  = payload.sim_is_rvc;
  ret.kanata_id   = payload.kanata_id;
`endif // SIMULATION

  return ret;
endfunction // assign_issue


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
    logic               valid;
    riscv_pkg::xlen_t   vaddr;
    mem_cmd_t           cmd;
    scariv_pkg::ic_strb_t size;
    logic               passthrough;
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
    scariv_pkg::paddr_t paddr;
  } tlb_resp_t;

  typedef struct packed {
    mem_cmd_t cmd;
    scariv_pkg::paddr_t addr;
    dc_color_t          color;
    dc_data_t data;
    dc_strb_t byte_en;
  } l2_req_t;

  typedef struct packed {
    dc_data_t data;
  } l2_resp_t;

typedef struct packed {
  dc_data_t           data;
  dc_ways_idx_t       way;
  scariv_pkg::paddr_t paddr;
  dc_color_t          color;
} evict_payload_t;

typedef struct packed {
  scariv_pkg::paddr_t paddr;
  dc_color_t          color;
  logic               is_uc;
  dc_ways_idx_t       way;
} mshr_req_t;

typedef struct packed {
  logic                          full;
  logic                          evict_conflict;
  logic                          allocated;
  logic [scariv_conf_pkg::MSHR_ENTRY_SIZE-1: 0] mshr_index_oh;
} mshr_resp_t;

typedef struct packed {
  logic               valid;
  scariv_pkg::paddr_t paddr;
  dc_color_t          color;
  logic               is_uc;
  logic               sent;
  logic               get_data;
  dc_data_t           data;
  dc_ways_idx_t       way;
} mshr_entry_t;

function mshr_entry_t assign_mshr_entry (logic valid, mshr_req_t req);
  mshr_entry_t ret;

  ret = 'h0;

  ret.valid = valid;
  ret.is_uc = req.is_uc;
  ret.way   = req.way;
  if (req.is_uc) begin
    ret.paddr = req.paddr;
  end else begin
    ret.paddr = {req.paddr[riscv_pkg::PADDR_W-1:$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W)],
                   {$clog2(scariv_lsu_pkg::DCACHE_DATA_B_W){1'b0}}};
    ret.color = req.color;
  end

  return ret;

endfunction // assign_mshr_entry

typedef struct packed {
  logic            valid;
  scariv_pkg::alen_t data;
  dc_strb_t        be;
} evict_merge_t;

typedef struct packed {
  logic          valid;
  logic [scariv_conf_pkg::MSHR_ENTRY_SIZE-1: 0] resolve_index_oh;
  logic [scariv_conf_pkg::MSHR_ENTRY_SIZE-1: 0] mshr_entry_valids;
} mshr_resolve_t;

typedef struct packed {
  logic valid;
  logic rs1;
  logic rs2;
  scariv_pkg::vaddr_t addr;
  // Temporary Disable
  // logic asid = UInt(width = asIdBits max 1) // TODO zero-width
} sfence_t;

typedef struct packed {
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;
  scariv_pkg::paddr_t  paddr;
  decoder_lsu_ctrl_pkg::size_t size; // Memory Access Size
  logic                success;
} ldq_ex2_update_t;

typedef struct packed {
  scariv_pkg::cmt_id_t          cmt_id;
  scariv_pkg::grp_id_t          grp_id;
  scariv_pkg::paddr_t           paddr;
  dc_color_t                    color;
  logic                         is_uc;
  decoder_lsu_ctrl_pkg::size_t  size; // Memory Access Size
  decoder_lsu_ctrl_pkg::rmwop_t rmwop;
  logic                         success; // SC is succeeded
} stq_ex2_update_t;


typedef struct packed {
  logic                                valid;
  scariv_pkg::cmt_id_t      cmt_id;
  scariv_pkg::grp_id_t grp_id;
  logic [riscv_pkg::PADDR_W-1: 3]      paddr;
  logic [ 7: 0]                        dw;
} ex2_addr_check_t;

// L1D interface
typedef struct packed {
  logic                                           s0_valid;
  logic                                           s0_tag_update_valid;
  dc_ways_idx_t                                   s0_way;
  scariv_pkg::paddr_t                             s0_paddr;
  dc_color_t                                      s0_color;
  logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]     s0_data;
  logic [DCACHE_DATA_B_W-1: 0]                    s0_be;
  scariv_lsu_pkg::mesi_t                          s0_mesi;
} dc_wr_req_t;

typedef struct packed {
  logic               s1_hit;
  logic               s1_miss;
  logic               s2_evicted_valid;
  scariv_pkg::paddr_t s2_evicted_paddr;
  dc_color_t          s2_evicted_color;
  dc_data_t           s2_evicted_data;
  mesi_t              s2_evicted_mesi;
} dc_wr_resp_t;

typedef struct packed {
  scariv_pkg::paddr_t            s0_paddr;
  dc_color_t                     s0_color;
  scariv_lsu_pkg::dc_data_t      s0_data;
  scariv_lsu_pkg::dc_strb_t      s0_be;
  dc_ways_idx_t                  s0_way;
  mesi_t                         s0_mesi;
} s0_l1d_wr_req_t;


typedef struct packed {
  logic s1_hit;
  logic s1_miss;
  logic s1_conflict;
} s1_l1d_wr_resp_t;


typedef struct packed {
  logic                  s2_evicted_valid;
  dc_data_t              s2_evicted_data;
  scariv_pkg::paddr_t    s2_evicted_paddr;
  dc_color_t             s2_evicted_color;
  scariv_lsu_pkg::mesi_t s2_evicted_mesi;
} s2_l1d_wr_resp_t;


typedef struct packed {
  logic          valid;
  logic          high_priority;
  dc_index_t     index;
  scariv_pkg::paddr_t paddr_d1;
} dc_read_req_t;

typedef struct packed {
  logic            hit;
  dc_ways_idx_t hit_way;
  logic            miss;
  logic            conflict;
  logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0] data;
  scariv_lsu_pkg::mesi_t                      mesi;
} dc_read_resp_t;

function automatic logic [scariv_pkg::ALEN_W/8 + scariv_pkg::ALEN_W-1: 0]
  fwd_align (decoder_lsu_ctrl_pkg::size_t size, scariv_pkg::alenb_t fwd_dw, scariv_pkg::alen_t fwd_data,
             logic [$clog2(scariv_pkg::ALEN_W/8)-1:0] paddr);

  scariv_pkg::alenb_t                  w_aligned_fwd_dw;
  scariv_pkg::alen_t                  w_aligned_fwd_data;

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
      w_aligned_fwd_dw   = fwd_dw   >> {paddr[$clog2(scariv_pkg::ALEN_W/8)-1], 2'b00};
      w_aligned_fwd_data = fwd_data >> {paddr[$clog2(scariv_pkg::ALEN_W/8)-1], 2'b00, 3'b000};
// `endif // RV32
    end
    decoder_lsu_ctrl_pkg::SIZE_H  : begin
      w_aligned_fwd_dw   = fwd_dw   >> {paddr[$clog2(scariv_pkg::ALEN_W/8)-1:1], 1'b0};
      w_aligned_fwd_data = fwd_data >> {paddr[$clog2(scariv_pkg::ALEN_W/8)-1:1], 1'b0, 3'b000};
    end
    decoder_lsu_ctrl_pkg::SIZE_B  : begin
      w_aligned_fwd_dw   = fwd_dw   >>  paddr[$clog2(scariv_pkg::ALEN_W/8)-1:0];
      w_aligned_fwd_data = fwd_data >> {paddr[$clog2(scariv_pkg::ALEN_W/8)-1:0], 3'b000};
    end
    default : begin
      w_aligned_fwd_dw   = 'h0;
      w_aligned_fwd_data = 'h0;
    end
  endcase // case (r_ex2_pipe_ctrl.size)

  return {w_aligned_fwd_dw, w_aligned_fwd_data};

endfunction // fwd_align


function scariv_pkg::alenb_t gen_dw(decoder_lsu_ctrl_pkg::size_t size, logic [$clog2(scariv_pkg::ALEN_W/8)-1:0] addr);
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


function scariv_pkg::alen_t align_8byte (logic [63: 0] data, logic [ 2: 0] pa);
  case (pa)
    'b000: return data;
    'b001: return {data[64- 8-1: 0],  8'h00};
    'b010: return {data[64-16-1: 0], 16'h00};
    'b011: return {data[64-24-1: 0], 24'h00};
    'b100: return {data[64-32-1: 0], 32'h00};
    'b101: return {data[64-40-1: 0], 40'h00};
    'b110: return {data[64-48-1: 0], 48'h00};
    'b111: return {data[64-56-1: 0], 56'h00};
    default : return 'h0;
  endcase // case (pa)
endfunction // align_8byte

function scariv_pkg::alen_t align_4byte (logic [31: 0] data, logic [ 1: 0] pa);
  case (pa)
    'b00: return data;
    'b01: return {data[32- 8-1: 0],  8'h00};
    'b10: return {data[32-16-1: 0], 16'h00};
    'b11: return {data[32-24-1: 0], 24'h00};
    default : return 'h0;
  endcase // case (pa)
endfunction // align_byte


// addr1/size1 includes addr2_dw ?
function logic is_dw_included(decoder_lsu_ctrl_pkg::size_t size1, logic [$clog2(scariv_pkg::ALEN_W/8)-1:0] addr1,
                              logic [scariv_pkg::ALEN_W/8-1:0] addr2_dw);
  scariv_pkg::alenb_t addr1_dw;
  addr1_dw = gen_dw(size1, addr1);

  return (addr1_dw & addr2_dw) == addr2_dw;
endfunction // is_dw_included

// addr1/size1 includes addr2_dw ?
function logic is_strb_hit(decoder_lsu_ctrl_pkg::size_t size1, logic [$clog2(scariv_pkg::ALEN_W/8)-1:0] addr1,
                           logic [scariv_pkg::ALEN_W/8-1:0] addr2_dw);
  scariv_pkg::alenb_t addr1_dw;
  addr1_dw = gen_dw(size1, addr1);

  return |(addr1_dw & addr2_dw);
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
// typedef enum logic[4:0] {
//   STQ_INIT          ,
//   STQ_TLB_HAZ       ,
//   STQ_ISSUE_WAIT    ,
//   STQ_DONE_EX2      ,
//   STQ_COMMIT        ,
//   STQ_WAIT_ST_DATA  ,
//   STQ_DEAD          ,
//   STQ_WAIT_COMMIT   ,
//   STQ_DONE_EX3      ,
//   STQ_ISSUED        ,
//   STQ_OLDEST_HAZ    ,
//   STQ_WAIT_OLDEST   ,
//   STQ_WAIT_STBUF
// } stq_state_t;

typedef struct packed {
  scariv_pkg::cmt_id_t   cmt_id;
  scariv_pkg::grp_id_t   grp_id;
  logic                  is_rmw;
  reg_rd_issue_t         rd_reg;
//  reg_wr_issue_t         wr_reg;
`ifdef SIMULATION
  logic [31: 0] sim_inst;
  inst_cat_t    sim_cat;
  logic [63: 0] sim_kanata_id;
  vaddr_t       sim_pc_addr;
`endif // SIMULATION
} stq_static_info_t;

typedef struct packed {
  logic            is_valid;
  // brtag_t          brtag;
  stq_static_info_t             inst;
  decoder_lsu_ctrl_pkg::size_t  size; // Memory Access Size

  logic                 dead;

  scariv_pkg::maxaddr_t addr;
  dc_color_t            color;
  logic                 paddr_valid;
  logic                 rs2_rel_read_accepted;
  logic                 rs2_phy_read_accepted;
  logic                 is_rs2_get;

  logic                is_committed;

  // Uncached Access Region
  logic                         is_uc;
  decoder_lsu_ctrl_pkg::rmwop_t rmwop;
  logic                         sc_success;

  logic st_buf_finished;
`ifdef SIMULATION
    logic [63: 0]                     kanata_id;
`endif // SIMULATION
} stq_entry_t;

typedef struct packed {
  logic [scariv_conf_pkg::STQ_SIZE-1: 0] index;
} stq_resolve_t;

typedef struct packed {
  logic          done;
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;
} store_op_t;

typedef struct packed {
  scariv_pkg::paddr_t paddr;
  decoder_lsu_ctrl_pkg::size_t   acc_size;
  scariv_pkg::alen_t data;
} srq_req_t;

typedef struct packed {
  logic                          full;
  logic                          conflict;
  logic [scariv_conf_pkg::MSHR_ENTRY_SIZE-1: 0] mshr_index_oh;
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

// typedef enum logic[3:0] {
//   LDQ_INIT           ,
//   LDQ_EX2_RUN        ,
//   LDQ_MSHR_WAIT     ,
//   LDQ_TLB_HAZ        ,
//   LDQ_ISSUE_WAIT     ,
//   LDQ_CHECK_ST_DEPEND,
//   LDQ_EX3_DONE       ,
//   LDQ_WAIT_COMMIT    ,
//   LDQ_WAIT_ENTRY_CLR ,
//   LDQ_ISSUED         ,
//   LDQ_MSHR_EVICT_HAZ  ,
//   LDQ_MSHR_FULL       ,
//   LDQ_WAIT_OLDEST    ,
//   LDQ_NONFWD_HAZ_WAIT
// } ldq_state_t;

typedef struct packed {
  scariv_pkg::cmt_id_t   cmt_id;
  scariv_pkg::grp_id_t   grp_id;
  logic                  oldest_valid;
`ifdef SIMULATION
  vaddr_t       sim_pc_addr;
  logic [31: 0] sim_inst;
  inst_cat_t    sim_cat;
  logic [63: 0] sim_kanata_id;
`endif // SIMULATION
} ldq_static_info_t;


typedef struct packed {
  logic          is_valid;
//  brtag_t brtag;
  // logic [scariv_conf_pkg::LSU_INST_NUM-1: 0]  pipe_sel_idx_oh;
  ldq_static_info_t inst;
  decoder_lsu_ctrl_pkg::size_t    size; // Memory Access Size
  // ldq_state_t                     state;
  logic                           is_get_data;
  // scariv_pkg::vaddr_t vaddr;
  // scariv_pkg::paddr_t paddr;
  scariv_pkg::maxaddr_t  addr;
  logic                  paddr_valid;
//  logic [scariv_conf_pkg::MSHR_ENTRY_SIZE-1: 0] mshr_haz_index_oh;
//  logic [scariv_conf_pkg::STQ_SIZE-1: 0]  hazard_index;

  logic                 dead;
  logic                 is_committed;

  logic                except_valid;
  scariv_pkg::except_t except_type;

`ifdef SIMULATION
    logic [63: 0]                     kanata_id;
`endif // SIMULATION

} ldq_entry_t;


typedef struct packed {
  logic                  valid;
  scariv_pkg::cmt_id_t   cmt_id;
  scariv_pkg::grp_id_t   grp_id;
  logic [31: 0]          inst;
  reg_rd_issue_t [ 2: 0] rd_regs;
  reg_wr_issue_t         wr_reg;
  logic                  oldest_valid;
  inst_cat_t             cat;

  logic                  l1d_high_priority;
  logic                  paddr_valid;
  scariv_pkg::paddr_t    paddr;
  dc_color_t             color;
  logic                  is_uc;

`ifdef SIMULATION
  logic [63: 0]          kanata_id;
  vaddr_t                sim_pc_addr;
`endif // SIMULATION
} lsu_pipe_issue_t;


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
  STATUS_MSHR_CONFLICT = 4
} lsu_status_t;


// Snoop interface

typedef struct packed {
  scariv_pkg::paddr_t paddr;
  dc_color_t          color;
} snoop_req_t;

typedef struct packed {
  logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0] data;
  logic [DCACHE_DATA_B_W-1: 0] be;
} snoop_resp_t;

typedef enum logic {
  SNOOP_READ,
  SNOOP_INVALID
} l1d_snp_cmd_t;

// -----------------------
// Store Buffer Interface
// -----------------------
function automatic integer max(integer a, integer b);
  return a > b ? a : b;
endfunction // max
function automatic integer min(integer a, integer b);
  return a < b ? a : b;
endfunction // max

localparam ST_BUF_WIDTH = min(scariv_pkg::ALEN_W * 2, scariv_conf_pkg::DCACHE_DATA_W);
localparam ST_BUF_ENTRY_SIZE = scariv_conf_pkg::STQ_SIZE / 4;

typedef enum logic [1:0] {
  ST_BUF_ALLOC = 0,
  ST_BUF_MERGE = 1,
  ST_BUF_FULL  = 2
} st_buffer_resp_t;

typedef struct packed {
  logic                                                valid;
  scariv_pkg::paddr_t                                  paddr;
  dc_color_t                                           color;
  logic [ST_BUF_WIDTH/8-1:0]                           strb;
  logic [ST_BUF_WIDTH-1: 0]                            data;
  logic [scariv_conf_pkg::MSHR_ENTRY_SIZE-1: 0]       mshr_index_oh;
  dc_ways_idx_t                                        l1d_way;
  logic                                                l1d_high_priority;
  decoder_lsu_ctrl_pkg::rmwop_t                        rmwop;
  decoder_lsu_ctrl_pkg::size_t                         size;
  logic                                                is_amo;
  logic                                                amo_op_done;
`ifdef SIMULATION
  scariv_pkg::cmt_id_t cmt_id;
  scariv_pkg::grp_id_t grp_id;
`endif // SIMULATION
} st_buffer_entry_t;

typedef enum logic [ 3: 0] {
  ST_BUF_INIT          = 0,
  ST_BUF_RD_L1D        = 1,
  ST_BUF_RESP_L1D      = 2,
  ST_BUF_L1D_UPDATE    = 3,
  ST_BUF_L1D_UPD_RESP  = 4,
  ST_BUF_MSHR_REFILL  = 5,
  ST_BUF_WAIT_REFILL   = 6,
  ST_BUF_WAIT_FULL     = 7,
  ST_BUF_WAIT_EVICT    = 8,
  ST_BUF_L1D_MERGE     = 9,
  ST_BUF_L1D_MERGE2    = 10,
  ST_BUF_WAIT_FINISH   = 11,
  ST_BUF_AMO_OPERATION = 12,
  ST_BUF_WAIT_SNOOP    = 13
} st_buffer_state_t;

function st_buffer_entry_t assign_st_buffer (
`ifdef SIMULATION
   scariv_pkg::cmt_id_t cmt_id,
   scariv_pkg::grp_id_t grp_id,
`endif // SIMULATION
   scariv_pkg::paddr_t  paddr,
   dc_color_t           color,
   logic [ST_BUF_WIDTH/8-1: 0]   strb,
   logic [ST_BUF_WIDTH-1: 0]     data,
   decoder_lsu_ctrl_pkg::rmwop_t rmwop,
   decoder_lsu_ctrl_pkg::size_t  size
  );
  st_buffer_entry_t ret;

  ret = 'h0;

  ret.valid = 1'b1;
  ret.paddr = paddr[riscv_pkg::PADDR_W-1:0];
  ret.color = color;
  ret.strb  = strb;
  ret.data  = data;

  ret.rmwop  = rmwop;
  ret.size   = size;

`ifdef SIMULATION
  ret.cmt_id = cmt_id;
  ret.grp_id = grp_id;
`endif // SIMULATION

  return ret;
endfunction // assign_st_buffer


function automatic riscv_pkg::xlen_t mem_offset (decoder_lsu_ctrl_pkg::op_t op, logic [31: 0] inst);
  if (op == decoder_lsu_ctrl_pkg::OP_STORE) begin
    return {{(riscv_pkg::VADDR_W-12){inst[31]}}, inst[31:25], inst[11: 7]};
  end else if (op == decoder_lsu_ctrl_pkg::OP_LOAD) begin
    return {{(riscv_pkg::VADDR_W-12){inst[31]}}, inst[31:20]};
  end else begin
    return 'h0;
  end
endfunction // mem_offset


function automatic logic is_cache_addr_same(scariv_pkg::paddr_t pa0, scariv_pkg::paddr_t pa1);
  return pa0[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)] == pa1[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)];
endfunction // is_cache_addr_same

// LSU Replay Queue
typedef struct packed {
  logic [31: 0]              inst;
  scariv_pkg::cmt_id_t       cmt_id;
  scariv_pkg::grp_id_t       grp_id;
  inst_cat_t                 cat;
  logic                      oldest_valid;
  scariv_pkg::reg_rd_issue_t rd_reg;
  scariv_pkg::reg_wr_issue_t wr_reg;
  scariv_pkg::paddr_t        paddr;
  logic                      is_uc;
  scariv_lsu_pkg::ex2_haz_t  hazard_typ;
  dc_color_t                 color;
  logic [HAZARD_INDEX_SIZE-1: 0] hazard_index;
} lsu_replay_queue_t;

endpackage // scariv_lsu_pkg

interface iq_upd_if;
  import scariv_lsu_pkg::*;

  logic                         update;
  logic [LSU_IQ_ENTRY_SIZE-1:0] index_oh;
  ex1_haz_t                     hazard_typ;

  logic                         tlb_resolve;

modport master (output update, index_oh, hazard_typ, tlb_resolve);
modport slave  (input  update, index_oh, hazard_typ, tlb_resolve);

endinterface // iq_upd_if


interface ldq_upd_if;
  logic        ex2_update;
  scariv_lsu_pkg::ldq_ex2_update_t ex2_payload;

modport master (output ex2_update, ex2_payload);
modport slave  (input  ex2_update, ex2_payload);

endinterface // ldq_upd_if

interface stq_upd_if;
  logic        ex2_update;
  scariv_lsu_pkg::stq_ex2_update_t ex2_payload;

modport master (output ex2_update, ex2_payload);
modport slave  (input  ex2_update, ex2_payload);

endinterface // stq_upd_if
