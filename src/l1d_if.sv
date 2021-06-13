interface l1d_rd_if;

  logic                          s0_valid;
  logic [riscv_pkg::PADDR_W-1:0] s0_paddr;
  logic                                    s1_hit;
  logic                                    s1_miss;
  logic                                    s1_conflict;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1:0] s1_data;

  modport master(
    output s0_valid,
    output s0_paddr,
    input  s1_hit,
    input  s1_miss,
    input  s1_conflict,
    input  s1_data
  );

  modport slave(
    input  s0_valid,
    input  s0_paddr,
    output s1_hit,
    output s1_miss,
    output s1_conflict,
    output s1_data
  );

endinterface // l1d_rd_if


interface l1d_wr_if;

  logic valid;
  logic [riscv_pkg::PADDR_W-1:0] paddr;
  logic hit;
  logic miss;
  logic conflict;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1:0] data;
  logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1:0] be;

  modport master(
    output valid,
    output paddr,
    input hit,
    input miss,
    input conflict,
    output data,
    output be
  );

  modport slave(
    input valid,
    input paddr,
    output hit,
    output miss,
    output conflict,
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
