interface disp_if;
  mrh_pkg::disp_t[mrh_pkg::DISP_SIZE-1:0] inst;
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
