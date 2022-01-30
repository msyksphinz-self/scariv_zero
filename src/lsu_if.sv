interface l1d_rd_if;

  logic                          s0_valid;
  logic [riscv_pkg::PADDR_W-1:0] s0_paddr;
  logic                          s0_h_pri;   // Highest Priority (used for when L1D eviction swap)
  logic                                    s1_hit;
  logic [$clog2(msrh_conf_pkg::DCACHE_WAYS)-1: 0] s1_hit_way;
  logic                                    s1_miss;
  logic                                    s1_conflict;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1:0] s1_data;

  // Eviction: Replaced Address
  logic                                           s1_replace_valid;
  logic [$clog2(msrh_conf_pkg::DCACHE_WAYS)-1: 0] s1_replace_way;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0]       s1_replace_data;
  logic [riscv_pkg::PADDR_W-1: 0]                 s1_replace_paddr;

  modport master(
    output s0_valid,
    output s0_paddr,
    output s0_h_pri,
    input  s1_hit,
    input  s1_hit_way,
    input  s1_miss,
    input  s1_conflict,
    input  s1_data,

    input  s1_replace_valid,
    input  s1_replace_way,
    input  s1_replace_data,
    input  s1_replace_paddr
  );

  modport slave(
    input  s0_valid,
    input  s0_paddr,
    input  s0_h_pri,
    output s1_hit,
    output s1_hit_way,
    output s1_miss,
    output s1_conflict,
    output s1_data,

    output s1_replace_valid,
    output s1_replace_way,
    output s1_replace_data,
    output s1_replace_paddr
  );

endinterface // l1d_rd_if


interface l1d_wr_if;

  logic valid;
  logic [riscv_pkg::PADDR_W-1:0] paddr;
  logic hit;
  logic miss;
  logic conflict;
  logic [$clog2(msrh_conf_pkg::DCACHE_WAYS)-1: 0] way;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1:0] data;
  logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1:0] be;

  modport master(
    output valid,
    output paddr,
    input hit,
    input miss,
    input conflict,
    output way,
    output data,
    output be
  );

  modport slave(
    input valid,
    input paddr,
    output hit,
    output miss,
    output conflict,
    input way,
    input data,
    input be
  );

endinterface // l1d_wr_if


interface l1d_lrq_if;
  logic load;
  msrh_lsu_pkg::lrq_req_t  req_payload;
  msrh_lsu_pkg::lrq_resp_t resp_payload;

  modport master (
    output load,
    output req_payload,
    input  resp_payload
  );

  modport slave (
    input  load,
    input  req_payload,
    output resp_payload
  );

endinterface // l1d_lrq_if


// Search Interface
// from STQ --> LRQ Eviction
// to search hitting eviction address
interface lrq_evict_search_if;
logic                                    valid;
logic [msrh_lsu_pkg::DCACHE_TAG_LOW-1:0] tag_low;
logic [msrh_conf_pkg::DCACHE_WAYS-1: 0]  hit_ways;

modport master (
  output valid,
  output tag_low,
  input  hit_ways
);

modport slave (
  input  valid,
  input  tag_low,
  output hit_ways
);

endinterface // lrq_evict_search_if


interface l1d_srq_if;
  logic load;
  msrh_lsu_pkg::srq_req_t  req_payload;
  msrh_lsu_pkg::srq_resp_t resp_payload;

modport master (
  output load,
  output req_payload,
  input  resp_payload
);

modport slave (
  input  load,
  input  req_payload,
  output resp_payload
);

endinterface // l1d_srq_if


interface l1d_evict_if;
logic    valid;
logic    ready;
msrh_lsu_pkg::evict_payload_t payload;

modport master (
  output valid,
  input  ready,
  output payload
);

modport slave (
  input  valid,
  output ready,
  input  payload
  );

endinterface // l1d_evict_if

interface lrq_dc_search_if;

logic valid;
logic [msrh_pkg::LRQ_ENTRY_W-1: 0] index;
msrh_lsu_pkg::lrq_entry_t lrq_entry;

modport master (
  output valid,
  output index,
  input  lrq_entry
);

modport slave (
  input  valid,
  input  index,
  output lrq_entry
);

endinterface // lrq_dc_search_if


interface lrq_pa_search_if;

logic                                 s0_valid;
logic [riscv_pkg::PADDR_W-1: 0]       s0_paddr;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] s1_hit_index_oh;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] s1_evict_hit_index_oh;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] s1_evict_sent;

modport master (
  output s0_valid,
  output s0_paddr,
  input  s1_hit_index_oh,
  input  s1_evict_hit_index_oh,
  input  s1_evict_sent
);

modport slave (
  input  s0_valid,
  input  s0_paddr,
  output s1_hit_index_oh,
  output s1_evict_hit_index_oh,
  output s1_evict_sent
);

endinterface // lrq_pa_search_if


interface lsu_replay_if;

logic    valid;
msrh_pkg::issue_t issue;
logic [msrh_lsu_pkg::MEM_Q_SIZE-1: 0] index_oh;
logic                                 conflict;

modport master (
  output valid,
  output issue,
  output index_oh,
  input  conflict
);

modport slave (
  input  valid,
  input  issue,
  input  index_oh,
  output conflict
);

endinterface // lsu_replay_if


interface fwd_check_if;

logic                           valid;
logic [msrh_pkg::CMT_ID_W-1:0] cmt_id;
logic [msrh_conf_pkg::DISP_SIZE-1:0] grp_id;
logic [riscv_pkg::PADDR_W-1: 0] paddr;
logic [riscv_pkg::XLEN_W/8-1: 0] paddr_dw;
logic                           fwd_valid;
logic [riscv_pkg::XLEN_W/8-1: 0] fwd_dw;
logic [riscv_pkg::XLEN_W-1: 0]  fwd_data;

modport master (
  output valid,
  output cmt_id,
  output grp_id,
  output paddr,
  output paddr_dw,
  input  fwd_valid,
  input  fwd_dw,
  input  fwd_data
);

modport slave (
  input  valid,
  input  cmt_id,
  input  grp_id,
  input  paddr,
  input  paddr_dw,
  output fwd_valid,
  output fwd_dw,
  output fwd_data
);

endinterface // fwd_check_if

interface lrq_haz_check_if;
logic                                 ex2_valid;
logic [riscv_pkg::PADDR_W-1: 0]       ex2_paddr;
logic                                 ex2_evict_haz_valid;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] ex2_evict_entry_idx;

modport master
  (
   output ex2_valid,
   output ex2_paddr,
   input  ex2_evict_haz_valid,
   input  ex2_evict_entry_idx
   );

modport slave
  (
   input  ex2_valid,
   input  ex2_paddr,
   output ex2_evict_haz_valid,
   output ex2_evict_entry_idx
   );

endinterface // lrq_haz_check_if


interface ldq_haz_check_if;
logic                                 ex2_valid;
logic [riscv_pkg::PADDR_W-1: 0]       ex2_paddr;
logic [msrh_pkg::CMT_ID_W-1:0]        ex2_cmt_id;
logic [msrh_conf_pkg::DISP_SIZE-1:0]  ex2_grp_id;
decoder_lsu_ctrl_pkg::size_t          ex2_size;
logic                                 ex3_haz_valid;
logic [msrh_pkg::CMT_ID_W-1:0]        ex3_haz_cmt_id;
logic [msrh_conf_pkg::DISP_SIZE-1:0]  ex3_haz_grp_id;

modport master
  (
   output ex2_valid,
   output ex2_paddr,
   output ex2_cmt_id,
   output ex2_grp_id,
   output ex2_size,
   input  ex3_haz_valid,
   input  ex3_haz_cmt_id,
   input  ex3_haz_grp_id
   );

modport slave
  (
   input  ex2_valid,
   input  ex2_paddr,
   input  ex2_cmt_id,
   input  ex2_grp_id,
   input  ex2_size,
   output ex3_haz_valid,
   output ex3_haz_cmt_id,
   output ex3_haz_grp_id
   );

endinterface // ldq_haz_check_if


interface tlb_ptw_if;

  msrh_lsu_pkg::ptw_req_t        req;
  logic    req_ready;
  msrh_lsu_pkg::ptw_resp_t       resp;
  logic    resp_ready;
  logic [riscv_pkg::XLEN_W-1: 0] satp;
  logic [riscv_pkg::XLEN_W-1: 0] status;
  // msrh_lsu_pkg::pmp_t            pmp[msrh_lsu_pkg::PMP_NUM];

  modport master (
    output req,
    input  req_ready,
    input  resp,
    output resp_ready,
    output satp,
    output status
    // input pmp
  );

  modport slave (
    input req,
    output req_ready,
    output resp,
    input  resp_ready,
    input  satp,
    input  status
    // input pmp
  );

endinterface // tlb_ptw_if


interface datapath_ptw_if;
  logic [riscv_pkg::XLEN_W-1: 0] satp;
  // sfence_req_t sfence;
  logic [riscv_pkg::XLEN_W-1: 0] status;
  // logic [PMP_NUM-1: 0]           pmp;
  // ptw_perf_events_t              perf;

  modport master (
    input  satp,
    // input  sfence,
    input  status
    // input  pmp,
    // output perf
  );

  modport slave (
    output satp,
    // output sfence,
    output status
    // output pmp,
    // input  perf
  );

endinterface // datapath_ptw_if


// Currently only read supports
interface lsu_access_if;

  logic                           req_valid;
  logic [riscv_pkg::PADDR_W-1: 0] paddr;
  decoder_lsu_ctrl_pkg::size_t    size;

  logic                           resp_valid;
  msrh_lsu_pkg::lsu_status_t      status;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_conflicted_idx_oh;

  logic [riscv_pkg::XLEN_W-1: 0]  data;

  logic                                 conflict_resolve_vld;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] conflict_resolve_idx_oh;

  modport master (
    output req_valid,
    output paddr,
    output size,
    input  resp_valid,
    input  status,
    input  lrq_conflicted_idx_oh,
    input  data,
    input  conflict_resolve_vld,
    input  conflict_resolve_idx_oh
  );

  modport slave (
    input  req_valid,
    input  paddr,
    input  size,
    output resp_valid,
    output status,
    output lrq_conflicted_idx_oh,
    output data,
    output conflict_resolve_vld,
    output conflict_resolve_idx_oh
  );

endinterface // lsu_access_if

//
// SFENCE interface for updating TLB
//
interface sfence_if;
  logic      valid;
  logic      is_rs1_x0;
  logic      is_rs2_x0;
  logic [riscv_pkg::VADDR_W-1: 0] vaddr;

  modport master (
    output valid,
    output is_rs1_x0,
    output is_rs2_x0,
    output vaddr
  );

  modport slave (
    input valid,
    input is_rs1_x0,
    input is_rs2_x0,
    input vaddr
  );

endinterface // sfence_if


interface snoop_if;
  logic     req_valid;
  logic     resp_valid;

  msrh_lsu_pkg::snoop_req_t  req_payload;
  msrh_lsu_pkg::snoop_resp_t resp_payload;

  modport master (
    output req_valid,
    output req_payload,
    input  resp_valid,
    input  resp_payload
  );

  modport slave (
    input  req_valid,
    input  req_payload,
    output resp_valid,
    output resp_payload
  );

endinterface // snoop_if


interface snoop_unit_if;
  logic                     req_valid;
  msrh_lsu_pkg::snoop_req_t req_payload;

  // L1D interface
  logic                      resp_valid;
  msrh_lsu_pkg::snoop_resp_t resp_payload;

  modport master (
    output req_valid,
    output req_payload,
    input  resp_valid,
    input  resp_payload
  );

  modport slave (
    input  req_valid,
    input  req_payload,
    output resp_valid,
    output resp_payload
  );

endinterface // snoop_unit_if


interface l1d_snoop_if;
  logic                           req_s0_valid;
  logic [riscv_pkg::PADDR_W-1: 0] req_s0_paddr ;

  logic                                      resp_s1_valid;
  msrh_lsu_pkg::lsu_status_t                 resp_s1_status;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0]  resp_s1_data;
  logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1: 0] resp_s1_be;

  modport master (
    output req_s0_valid,
    output req_s0_paddr,
    input  resp_s1_valid,
    input  resp_s1_status,
    input  resp_s1_data,
    input  resp_s1_be
  );

  modport slave (
    input  req_s0_valid,
    input  req_s0_paddr,
    output resp_s1_valid,
    output resp_s1_status,
    output resp_s1_data,
    output resp_s1_be
  );

endinterface // l1d_snoop_if


interface stq_snoop_if;
  logic                           req_s0_valid;
  logic [riscv_pkg::PADDR_W-1: 0] req_s0_paddr ;

  logic                                      resp_s1_valid;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0]  resp_s1_data;
  logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1: 0] resp_s1_be;

  modport master (
    output req_s0_valid,
    output req_s0_paddr,

    input  resp_s1_valid,
    input  resp_s1_data,
    input  resp_s1_be
  );

  modport slave (
    input  req_s0_valid,
    input  req_s0_paddr,

    output resp_s1_valid,
    output resp_s1_data,
    output resp_s1_be
  );

endinterface // stq_snoop_if


interface st_buffer_if;
logic                                     valid;
logic [riscv_pkg::PADDR_W-1: 0]           paddr;
logic [msrh_lsu_pkg::ST_BUF_WIDTH/8-1: 0] strb;
logic [msrh_lsu_pkg::ST_BUF_WIDTH-1: 0]   data;

msrh_lsu_pkg::st_buffer_resp_t resp;

modport master (
  output valid,
  output paddr,
  output strb,
  output data,
  input  resp
);


modport slave (
  input valid,
  input paddr,
  input strb,
  input data,
  output resp
);

endinterface // st_buffer_if
