interface csr_rd_if;

  logic valid;
  logic [11: 0] addr;
  logic [riscv_pkg::XLEN_W-1: 0] data;

  modport master (
    output valid,
    output addr,
    input  data
  );

  modport slave (
    input  valid,
    input  addr,
    output data
  );

endinterface // csr_rd_if


interface csr_wr_if;

  logic valid;
  logic [11: 0] addr;
  logic [riscv_pkg::XLEN_W-1: 0] data;

  modport master (
    output valid,
    output addr,
    output data
  );

  modport slave (
    input valid,
    input addr,
    input data
  );

endinterface // csr_wr_if


interface csr_info_if;
logic [riscv_pkg::XLEN_W-1: 0] mepc;
logic [riscv_pkg::XLEN_W-1: 0] mtvec;

modport master (
  output mepc,
  output mtvec
);

modport slave (
  input mepc,
  input mtvec
);

endinterface // csr_info_if
