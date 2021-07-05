interface l1d_rd_if;

  logic                          s0_valid;
  logic [riscv_pkg::PADDR_W-1:0] s0_paddr;
  logic                          s0_h_pri;   // Highest Priority (used for when L1D eviction swap)
  logic                                    s1_hit;
  logic                                    s1_miss;
  logic                                    s1_conflict;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1:0] s1_data;

  // Eviction: Replaced Address
  logic                                     s1_replace_valid;
  logic [msrh_conf_pkg::DCACHE_WAYS-1: 0]   s1_replace_way;
  logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] s1_replace_data;
  logic [riscv_pkg::PADDR_W-1: 0]           s1_replace_paddr;

  modport master(
    output s0_valid,
    output s0_paddr,
    output s0_h_pri,
    input  s1_hit,
    input  s1_miss,
    input  s1_conflict,
    input  s1_data,

    input  s1_replace_valid,
    input  s1_replace_way,
    input  s1_replace_data,
    input  s1_replace_paddr
  );

  modport slave(
    input  s0_valid,
    input  s0_paddr,
    input  s0_h_pri,
    output s1_hit,
    output s1_miss,
    output s1_conflict,
    output s1_data,

    output s1_replace_valid,
    output s1_replace_way,
    output s1_replace_data,
    output s1_replace_paddr
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


// Search Interface
// from STQ --> LRQ Eviction
// to search hitting eviction address
interface lrq_evict_search_if;
logic                            s0_valid;
logic [riscv_pkg::PADDR_W-1:0]   s0_paddr;
logic [riscv_pkg::XLEN_W-1: 0]   s0_data;
logic [riscv_pkg::XLEN_W/8-1: 0] s0_strb;

logic                            s1_hit_merged;

modport master (
  output s0_valid,
  output s0_paddr,
  output s0_data,
  output s0_strb,

  input  s1_hit_merged
);

modport slave (
  input  s0_valid,
  input  s0_paddr,
  input  s0_data,
  input  s0_strb,

  output s1_hit_merged
);

endinterface // lrq_evict_search_if


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


interface l1d_evict_if;
logic    valid;
logic    ready;
msrh_lsu_pkg::evict_payload_t payload;

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
