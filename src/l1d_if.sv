interface l1d_if;

  logic valid;
  logic [riscv_pkg::PADDR_W-1:0] paddr;
  logic hit;
  logic miss;
  logic conflict;
  logic [msrh_lsu_pkg::DCACHE_DATA_W-1:0] data;

  modport master(
    output valid,
    output paddr,
    input hit,
    input miss,
    input conflict,
    input data
  );

  modport slave(
    input valid,
    input paddr,
    output hit,
    output miss,
    output conflict,
    output data
  );

endinterface // l1d_if

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
