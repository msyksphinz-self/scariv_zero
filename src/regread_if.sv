interface regread_if;

  logic valid;
  msrh_pkg::rnid_t rnid;
  msrh_pkg::reg_t reg_type;
  logic resp;
  logic [riscv_pkg::XLEN_W-1:0] data;

  modport master(output valid, output rnid, input resp, input data);

  modport slave(input valid, input rnid, output resp, output data);

endinterface
