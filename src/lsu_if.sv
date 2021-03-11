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
logic [riscv_pkg::PADDR_W-1: 0] paddr;
logic                           fwd_vld;
logic [riscv_pkg::XLEN_W-1: 0]  fwd_data;

modport master (
  output valid,
  output paddr,
  input  fwd_vld,
  input  fwd_data
);

modport slave (
  input  valid,
  input  paddr,
  output fwd_vld,
  output fwd_data
);

endinterface // fwd_check_if
