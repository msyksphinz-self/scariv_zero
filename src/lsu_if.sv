interface lrq_search_if;

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

endinterface // lrq_search_if


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
logic [riscv_pkg::PADDR_W-1: 3] paddr;
logic [ 7: 0]                   paddr_dw;
logic                           fwd_valid;
logic [ 7: 0]                   fwd_dw;
logic [riscv_pkg::XLEN_W-1: 0]  fwd_data;
logic                           stq_hazard_vld;
logic [msrh_lsu_pkg::MEM_Q_SIZE-1: 0] stq_hazard_idx;

modport master (
  output valid,
  output cmt_id,
  output grp_id,
  output paddr,
  output paddr_dw,
  input  fwd_valid,
  input  fwd_dw,
  input  fwd_data,
  input  stq_hazard_vld,
  input  stq_hazard_idx
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
  output stq_hazard_vld,
  output stq_hazard_idx
);

endinterface // fwd_check_if


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
    input  ptbr,
    input  status
    // input pmp
  );

  modport slave (
    input req,
    output req_ready,
    output resp,
    input  resp_ready,
    output ptbr,
    output status
    // input pmp
  );

endinterface // tlb_ptw_if


interface datapath_ptw_if;
  logic [riscv_pkg::XLEN_W-1: 0] ptbr;
  sfence_req_t sfence;
  logic [riscv_pkg::XLEN_W-1: 0] status;
  logic [PMP_NUM-1: 0]           pmp_t;
  ptw_perf_events_t              perf;

  modport master (
    input  ptbr,
    input  sfence,
    input  status,
    input  pmp,
    output perf
  );

  modport slave (
    output ptbr,
    output sfence,
    output status,
    output pmp,
    input  perf
  );

endinterface // datapath_ptw_if
