interface regread_if;

  logic valid;
  logic [mrh_pkg::RNID_W-1:0] rnid;
  mrh_pkg::reg_t reg_type;
  logic resp;
  logic [riscv_pkg::XLEN_W-1:0] data;

  modport master(output valid, output rnid, input resp, input data);

  modport slave(input valid, input rnid, output resp, output data);

endinterface
