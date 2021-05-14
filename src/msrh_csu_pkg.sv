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

msrh_pkg::priv_t                priv;
logic [riscv_pkg::XLEN_W-1: 0] mstatus;
logic [riscv_pkg::XLEN_W-1: 0] mepc;
logic [riscv_pkg::XLEN_W-1: 0] mtvec;
logic [riscv_pkg::XLEN_W-1: 0] sepc;
logic [riscv_pkg::XLEN_W-1: 0] uepc;
logic [riscv_pkg::XLEN_W-1: 0] satp;

modport master (
  output priv,
  output mstatus,
  output mepc,
  output mtvec,
  output sepc,
  output uepc,
  output satp
);

modport slave (
  input priv,
  input mstatus,
  input mepc,
  input mtvec,
  input sepc,
  input uepc,
  input satp
);

endinterface // csr_info_if
