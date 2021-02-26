interface l1d_lrq_if;
  logic load;
  logic [riscv_pkg::PADDR_W-1:0] paddr;
  logic                          full;
  logic                          conflict;
  logic [msrh_pkg::LRQ_ENTRY_SIZE-1: 0] lrq_index_oh;

modport master (
  output load,
  output paddr,
  input  full,
  input  conflict,
  input  lrq_index_oh
);

modport slave (
  input  load,
  input  paddr,
  output full,
  output conflict,
  output lrq_index_oh
);

endinterface // l1d_lrq_if
