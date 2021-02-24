interface l1d_lrq_if;
  logic load;
  logic [riscv_pkg::PADDR_W-1:0] paddr;
  logic                          full;
  logic                          conflict;

modport master (
  output load,
  output paddr,
  input  full,
  input  conflict
);

modport slave (
  input  load,
  input  paddr,
  output full,
  output conflict
);

endinterface // l1d_lrq_if
