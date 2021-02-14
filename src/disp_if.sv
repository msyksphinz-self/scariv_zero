interface disp_if;
  /* verilator lint_off UNOPTFLAT */
  logic [msrh_pkg::CMT_BLK_W-1:0] cmt_id;
  msrh_pkg::disp_t[msrh_pkg::DISP_SIZE-1:0] inst;
  logic valid;
  logic ready;
  modport master(
    output valid,
    output inst,
    input ready
  );
  modport slave(
    input valid,
    input inst,
    output ready
  );
endinterface
