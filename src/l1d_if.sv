interface l1d_if;

  logic valid;
  logic [riscv_pkg::PADDR_W-1:0] paddr;
  logic hit;
  logic miss;
  logic [msrh_lsu_pkg::DCACHE_DATA_W-1:0] data;

  modport master(
    output valid,
    output paddr,
    input hit,
    input miss,
    input data
  );

  modport slave(
    input valid,
    input paddr,
    output hit,
    output miss,
    output data
  );

endinterface // l1d_if
