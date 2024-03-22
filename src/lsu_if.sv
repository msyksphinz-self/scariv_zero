interface l1d_rd_if;

import scariv_pkg::*;
import scariv_lsu_pkg::*;

logic      s0_valid;
dc_index_t s0_index;
logic      s0_high_priority;

paddr_t    s1_paddr;

logic      s2_hit;
dc_ways_t  s2_hit_way;
logic      s2_miss;
logic      s2_conflict;
mesi_t     s2_mesi;
dc_data_t  s2_data;

// Eviction: Replaced Address
logic     s2_replace_valid;
dc_ways_t s2_replace_way;
mesi_t    s2_replace_mesi;

modport master(output s0_valid, s0_index, s0_high_priority,
               output s1_paddr,
               input  s2_hit, s2_hit_way, s2_miss, s2_conflict, s2_data, s2_mesi,
               input  s2_replace_valid, s2_replace_way, s2_replace_mesi);
modport slave (input  s0_valid, s0_index, s0_high_priority,
               input  s1_paddr,
               output s2_hit, s2_hit_way, s2_miss, s2_conflict, s2_data, s2_mesi,
               output s2_replace_valid, s2_replace_way, s2_replace_mesi);
modport watch (input  s2_hit, s2_hit_way, s2_miss, s2_conflict, s2_data, s2_mesi,
               input  s2_replace_valid, s2_replace_way, s2_replace_mesi);

endinterface // l1d_rd_if


interface l1d_wr_if;

  logic                           s0_valid;
  scariv_lsu_pkg::s0_l1d_wr_req_t s0_wr_req;
  scariv_lsu_pkg::mesi_t          s0_mesi;
  logic                           s0_unlock_valid;

  logic                          s1_resp_valid;
  scariv_lsu_pkg::s1_l1d_wr_resp_t s1_wr_resp;
  logic                          s2_done;
  scariv_lsu_pkg::s2_l1d_wr_resp_t s2_wr_resp;

  modport master(
    output s0_valid,
    output s0_wr_req,
    output s0_unlock_valid,
    input  s1_resp_valid,
    input  s1_wr_resp,
    input  s2_done,
    input  s2_wr_resp
  );

  modport slave(
    input  s0_valid,
    input  s0_wr_req,
    input  s0_unlock_valid,
    output s1_resp_valid,
    output s1_wr_resp,
    output s2_done,
    output s2_wr_resp
  );

  modport watch (
    input s1_resp_valid,
    input s1_wr_resp,
    input s2_done,
    input s2_wr_resp
  );

  modport missunit_watch(
    input  s0_valid,
    input  s0_wr_req,
    input  s0_unlock_valid
  );

endinterface // l1d_wr_if


interface l1d_missu_if;
  logic load;
  scariv_lsu_pkg::missu_req_t  req_payload;
  scariv_lsu_pkg::missu_resp_t resp_payload;

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

endinterface // l1d_missu_if


// Search Interface
// from STQ --> LRQ Eviction
// to search hitting eviction address
interface missu_evict_search_if;
logic                                    valid;
logic [scariv_lsu_pkg::DCACHE_TAG_LOW-1:0] tag_low;
logic [scariv_conf_pkg::DCACHE_WAYS-1: 0]  hit_ways;

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

endinterface // missu_evict_search_if


interface mshr_stbuf_search_if;
  logic [scariv_pkg::MISSU_ENTRY_SIZE-1: 0]    mshr_index_oh;
  logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0] stbuf_be;
  logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]  stbuf_data;

  modport master (
    output mshr_index_oh,
    input  stbuf_be,
    input  stbuf_data
  );

  modport slave (
    input  mshr_index_oh,
    output stbuf_be,
    output stbuf_data
  );

endinterface // mshr_stbuf_search_if


interface l1d_srq_if;
  logic load;
  scariv_lsu_pkg::srq_req_t  req_payload;
  scariv_lsu_pkg::srq_resp_t resp_payload;

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
scariv_lsu_pkg::evict_payload_t payload;

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

interface missu_dc_search_if;

logic valid;
logic [scariv_pkg::MISSU_ENTRY_W-1: 0] index;
scariv_lsu_pkg::mshr_entry_t missu_entry;

modport master (
  output valid,
  output index,
  input  missu_entry
);

modport slave (
  input  valid,
  input  index,
  output missu_entry
);

endinterface // missu_dc_search_if


interface missu_pa_search_if;

logic                                 s0_valid;
scariv_pkg::paddr_t       s0_paddr;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] s1_hit_index_oh;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] s1_hit_update_index_oh;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] s1_evict_hit_index_oh;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] s1_evict_sent;

modport master (
  output s0_valid,
  output s0_paddr,
  input  s1_hit_index_oh,
  input  s1_hit_update_index_oh,
  input  s1_evict_hit_index_oh,
  input  s1_evict_sent
);

modport slave (
  input  s0_valid,
  input  s0_paddr,
  output s1_hit_index_oh,
  output s1_hit_update_index_oh,
  output s1_evict_hit_index_oh,
  output s1_evict_sent
);

endinterface // missu_pa_search_if


interface ldq_replay_if;

logic                                   valid;
scariv_lsu_pkg::ldq_static_info_t       issue;
logic [scariv_lsu_pkg::MEM_Q_SIZE-1: 0] index_oh;
logic                                   conflict;

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

endinterface // ldq_replay_if

interface stq_replay_if;

logic                                   valid;
scariv_lsu_pkg::stq_static_info_t       issue;
logic [scariv_lsu_pkg::MEM_Q_SIZE-1: 0] index_oh;
logic                                   conflict;

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

endinterface // stq_replay_if


interface fwd_check_if;

logic                valid;
scariv_pkg::cmt_id_t cmt_id;
scariv_pkg::grp_id_t grp_id;
scariv_pkg::paddr_t  paddr;
scariv_pkg::alenb_t  paddr_dw;
logic                fwd_valid;
scariv_pkg::alenb_t  fwd_dw;
scariv_pkg::alen_t   fwd_data;

// Forward Miss: Only used in DETAIL_STLD_FWD
logic                                          fwd_miss_valid;
logic [$clog2(scariv_conf_pkg::STQ_SIZE)-1: 0] fwd_miss_haz_index;

modport master (
  output valid,
  output cmt_id,
  output grp_id,
  output paddr,
  output paddr_dw,
  input  fwd_valid,
  input  fwd_dw,
  input  fwd_data,
  input  fwd_miss_valid,
  input  fwd_miss_haz_index
);

modport slave (
  input  valid,
  input  cmt_id,
  input  grp_id,
  input  paddr,
  input  paddr_dw,
  output fwd_valid,
  output fwd_dw,
  output fwd_data,
  output fwd_miss_valid,
  output fwd_miss_haz_index
);

endinterface // fwd_check_if

interface missu_fwd_if;
logic                                     ex2_valid;
scariv_pkg::paddr_t           ex2_paddr;
logic                                     ex2_fwd_valid;
logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0] ex2_fwd_data;

modport master
  (
   output ex2_valid,
   output ex2_paddr,
   input  ex2_fwd_valid,
   input  ex2_fwd_data
   );

modport slave
  (
   input  ex2_valid,
   input  ex2_paddr,
   output ex2_fwd_valid,
   output ex2_fwd_data
   );

endinterface // missu_fwd_if


interface ldq_haz_check_if;
logic                                 ex2_valid;
scariv_pkg::paddr_t       ex2_paddr;
scariv_pkg::cmt_id_t        ex2_cmt_id;
scariv_pkg::grp_id_t  ex2_grp_id;
decoder_lsu_ctrl_pkg::size_t          ex2_size;
logic                                 ex3_haz_valid;
scariv_pkg::cmt_id_t        ex3_haz_cmt_id;
scariv_pkg::grp_id_t  ex3_haz_grp_id;

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

interface stq_haz_check_if;
logic                        ex2_valid;
scariv_pkg::paddr_t            ex2_paddr;
scariv_pkg::cmt_id_t           ex2_cmt_id;
scariv_pkg::grp_id_t           ex2_grp_id;
decoder_lsu_ctrl_pkg::size_t ex2_size;
logic                                ex2_haz_valid;
logic [scariv_conf_pkg::STQ_SIZE-1: 0] ex2_haz_index;

modport master
  (
   output ex2_valid,
   output ex2_paddr,
   output ex2_cmt_id,
   output ex2_grp_id,
   output ex2_size,
   input  ex2_haz_valid,
   input  ex2_haz_index
   );

modport slave
  (
   input  ex2_valid,
   input  ex2_paddr,
   input  ex2_cmt_id,
   input  ex2_grp_id,
   input  ex2_size,
   output ex2_haz_valid,
   output ex2_haz_index
   );

endinterface // stq_haz_check_if


interface rmw_order_check_if;
logic               ex2_valid;
scariv_pkg::cmt_id_t  ex2_cmt_id;
scariv_pkg::grp_id_t  ex2_grp_id;
logic               ex2_stq_haz_vld;
logic               ex2_stbuf_haz_vld;

modport master
  (
   output ex2_valid,
   output ex2_cmt_id,
   output ex2_grp_id,
   input  ex2_stq_haz_vld,
   input  ex2_stbuf_haz_vld
   );

modport slave
  (
   input  ex2_valid,
   input  ex2_cmt_id,
   input  ex2_grp_id,
   output ex2_stq_haz_vld,
   output ex2_stbuf_haz_vld
   );

endinterface // rmw_order_check_if


interface tlb_ptw_if;

  scariv_lsu_pkg::ptw_req_t        req;
  logic    req_ready;
  scariv_lsu_pkg::ptw_resp_t       resp;
  logic    resp_ready;
  riscv_pkg::xlen_t satp;
  riscv_pkg::xlen_t status;
  // scariv_lsu_pkg::pmp_t            pmp[scariv_lsu_pkg::PMP_NUM];

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
  riscv_pkg::xlen_t satp;
  // sfence_req_t sfence;
  riscv_pkg::xlen_t status;
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
  scariv_pkg::paddr_t paddr;
  decoder_lsu_ctrl_pkg::size_t    size;

  logic                           resp_valid;
  scariv_lsu_pkg::lsu_status_t      status;
  logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] missu_conflicted_idx_oh;

  riscv_pkg::xlen_t  data;

  logic                                 conflict_resolve_vld;
  logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] conflict_resolve_idx_oh;

  modport master (
    output req_valid,
    output paddr,
    output size,
    input  resp_valid,
    input  status,
    input  missu_conflicted_idx_oh,
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
    output missu_conflicted_idx_oh,
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
  scariv_pkg::vaddr_t vaddr;

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


interface snoop_info_if;
  logic     busy;

  modport master (
    output busy
  );

  modport monitor (
    input busy
  );

endinterface // snoop_info_if

interface snoop_if;
  logic     req_valid;
  logic     resp_valid;

  scariv_lsu_pkg::snoop_req_t  req_payload;
  scariv_lsu_pkg::snoop_resp_t resp_payload;

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


// interface snoop_unit_if;
//   logic                     req_valid;
//   scariv_lsu_pkg::snoop_req_t req_payload;
//
//   // L1D interface
//   logic                      resp_valid;
//   scariv_lsu_pkg::snoop_resp_t resp_payload;
//
//   modport master (
//     output req_valid,
//     output req_payload,
//     input  resp_valid,
//     input  resp_payload
//   );
//
//   modport slave (
//     input  req_valid,
//     input  req_payload,
//     output resp_valid,
//     output resp_payload
//   );
//
// endinterface // snoop_unit_if


interface l1d_snoop_if;
  logic                                        req_s0_valid;
  scariv_lsu_pkg::l1d_snp_cmd_t                req_s0_cmd;
  scariv_pkg::paddr_t                          req_s0_paddr ;
  logic [scariv_conf_pkg::DCACHE_WAYS-1: 0]    req_s0_ways;

  logic                                        resp_s1_valid;
  scariv_lsu_pkg::lsu_status_t                 resp_s1_status;
  logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]  resp_s1_data;
  logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0] resp_s1_be;
  logic [scariv_conf_pkg::DCACHE_WAYS-1: 0]    resp_s1_ways;

  modport master (
    output req_s0_valid,
    output req_s0_cmd,
    output req_s0_paddr,
    output req_s0_ways,
    input  resp_s1_valid,
    input  resp_s1_status,
    input  resp_s1_data,
    input  resp_s1_be,
    input  resp_s1_ways
  );

  modport slave (
    input  req_s0_valid,
    input  req_s0_cmd,
    input  req_s0_paddr,
    input  req_s0_ways,
    output resp_s1_valid,
    output resp_s1_status,
    output resp_s1_data,
    output resp_s1_be,
    output resp_s1_ways
  );

endinterface // l1d_snoop_if


interface stq_snoop_if;
  logic                           req_s0_valid;
  scariv_pkg::paddr_t req_s0_paddr ;

  logic                                      resp_s1_valid;
  logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]  resp_s1_data;
  logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0] resp_s1_be;

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


interface mshr_snoop_if;
  logic               req_s0_valid;
  scariv_pkg::paddr_t req_s0_paddr;
  logic                                        resp_s1_valid;
  logic                                        resp_s1_evict_valid;
  logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0] resp_s1_be;
  logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]  resp_s1_data;

  logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] resp_s1_hit_index;
  logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] entry_valid;
  logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] entry_resolved;

  // logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] s1_hit_evict_index;

  modport master (
    output req_s0_valid,
    output req_s0_paddr,

    input  resp_s1_valid,
    input  resp_s1_be,
    input  resp_s1_data,
    input  resp_s1_hit_index,
    input  resp_s1_evict_valid,
    input  entry_valid,
    input  entry_resolved
  );

  modport slave (
    input  req_s0_valid,
    input  req_s0_paddr,

    output resp_s1_valid,
    output resp_s1_be,
    output resp_s1_data,
    output resp_s1_hit_index,
    output resp_s1_evict_valid,
    output entry_valid,
    output entry_resolved
  );

endinterface // mshr_snoop_if


interface stbuf_snoop_if;
  logic                           req_s0_valid;
  scariv_pkg::paddr_t req_s0_paddr ;

  logic                                      resp_s1_valid;
  logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]  resp_s1_data;
  logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0] resp_s1_be;

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

endinterface // stbuf_snoop_if


interface streq_snoop_if;
  logic                           req_s0_valid;
  scariv_pkg::paddr_t req_s0_paddr ;

  logic                                        resp_s1_valid;
  logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]  resp_s1_data;
  logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0] resp_s1_be;

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

endinterface // streq_snoop_if


interface st_buffer_if;
logic                                     valid;
scariv_pkg::paddr_t                         paddr;
logic [scariv_lsu_pkg::ST_BUF_WIDTH/8-1: 0] strb;
logic [scariv_lsu_pkg::ST_BUF_WIDTH-1: 0]   data;
logic                                     is_rmw;
decoder_lsu_ctrl_pkg::rmwop_t             rmwop;
decoder_lsu_ctrl_pkg::size_t              size;

logic                                     is_empty;

`ifdef SIMULATION
scariv_pkg::cmt_id_t cmt_id;
scariv_pkg::grp_id_t grp_id;
`endif // SIMULATION

scariv_lsu_pkg::st_buffer_resp_t resp;

modport master (
  output valid,
  output paddr,
  output strb,
  output data,
  output is_rmw,
  output rmwop,
  output size,
`ifdef SIMULATION
  output cmt_id,
  output grp_id,
`endif // SIMULATION
  input  resp,
  input  is_empty
);


modport slave (
  input valid,
  input paddr,
  input strb,
  input data,
  input is_rmw,
  input rmwop,
  input size,
`ifdef SIMULATION
  input cmt_id,
  input grp_id,
`endif // SIMULATION
  output resp,
  output is_empty
);


modport monitor (
  input valid,
  input paddr,
  input strb,
  input data,
  input is_rmw,
  input rmwop,
`ifdef SIMULATION
  input cmt_id,
  input grp_id,
`endif // SIMULATION
  input resp,
  input is_empty
);

endinterface // st_buffer_if

interface amo_op_if;

logic                         valid;
decoder_lsu_ctrl_pkg::rmwop_t rmwop;
decoder_lsu_ctrl_pkg::size_t  size;
riscv_pkg::xlen_t             data0;
riscv_pkg::xlen_t             data1;
riscv_pkg::xlen_t             result;

modport master (
  output valid,
  output rmwop,
  output size,
  output data0,
  output data1,
  input  result
);

modport slave (
  input  valid,
  input  rmwop,
  input  size,
  input  data0,
  input  data1,
  output result
);

endinterface // amo_op_if


interface uc_write_if;

logic             valid;
logic             ready;
scariv_pkg::paddr_t paddr;
riscv_pkg::xlen_t data;
decoder_lsu_ctrl_pkg::size_t size;
logic             is_empty;

modport master (
  output valid,
  output paddr,
  output data,
  output size,
  input  is_empty,
  input  ready
);

modport slave (
  input  valid,
  input  paddr,
  input  data,
  input  size,
  output is_empty,
  output ready
);


modport monitor (
  input  valid,
  input  paddr,
  input  data,
  input  size,
  input  is_empty,
  input  ready
);

endinterface // uc_write_if


interface lrsc_if;

logic    lr_update_valid;
/* verilator lint_off UNOPTFLAT */
logic    sc_check_valid;
scariv_pkg::paddr_t paddr;
logic    sc_success;

modport master (
  output lr_update_valid,
  output sc_check_valid,
  output paddr,
  input  sc_success
);

modport slave (
  input  lr_update_valid,
  input  sc_check_valid,
  input  paddr,
  output sc_success
);

endinterface // lrsc_if

// LSU Pipeline to Replay Queue Interface
interface lsu_pipe_haz_if;
  logic                              valid;
  logic [31: 0]                      inst;
  scariv_lsu_pkg::lsu_replay_queue_t payload;
  logic                              full;

  modport master (
    output valid,
    output payload,
    input  full
  );

  modport slave (
    input  valid,
    input  payload,
    output full
  );


endinterface // lsu_pipe_haz_if


interface lsu_pipe_req_if;
  logic                      valid;
  logic                      ready;
  scariv_lsu_pkg::lsu_replay_queue_t payload;

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

endinterface // lsu_repaly_if


interface st_req_info_if;
logic               busy;
scariv_pkg::paddr_t paddr;

modport master (
  output busy,
  output paddr
);

modport monitor (
  input busy,
  input paddr
);

endinterface // st_req_info_if
