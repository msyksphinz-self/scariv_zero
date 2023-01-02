interface l2_req_if #(parameter TAG_W = scariv_lsu_pkg::L2_CMD_TAG_W);
  scariv_lsu_pkg::l2_req_t payload;
  logic [TAG_W-1:0] tag;
  logic valid;
  logic ready;
  modport master(
    output valid,
    output tag,
    output payload,
    input ready
  );
  modport slave(
    input valid,
    input tag,
    input payload,
    output ready
  );
endinterface // l2_req_if


interface l2_resp_if #(parameter TAG_W = scariv_lsu_pkg::L2_CMD_TAG_W);
  scariv_lsu_pkg::l2_resp_t payload;
  logic [TAG_W-1: 0] tag;
  logic valid;
  logic ready;
  modport master(
    input ready,
    output valid,
    output tag,
    output payload
  );
  modport slave(
    output ready,
    input valid,
    input tag,
    input payload
  );
endinterface // l2_resp_if
