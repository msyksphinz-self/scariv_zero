interface l2_req_if;
  msrh_lsu_pkg::l2_req_t payload;
  logic valid;
  logic ready;
  modport master(
    output valid,
    output payload,
    input ready
  );
  modport slave(
    input valid,
    input payload,
    output ready
  );
endinterface

interface l2_resp_if;
  msrh_lsu_pkg::l2_resp_t payload;
  logic valid;
  logic ready;
  modport master(
    input ready,
    output valid,
    output payload
  );
  modport slave(
    output ready,
    input valid,
    input payload
  );
endinterface
