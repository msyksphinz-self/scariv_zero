interface regread_if #(parameter REG_TYPE = msrh_pkg::GPR);

  localparam WDITH_W = REG_TYPE == msrh_pkg::GPR ? riscv_pkg::XLEN_W : riscv_fpu_pkg::FLEN_W;

  logic                valid;
  msrh_pkg::rnid_t     rnid;
  msrh_pkg::reg_t      reg_type;
  logic                resp;
  logic [WDITH_W-1: 0] data;

  modport master(output valid, output rnid, input resp, input data);

  modport slave(input valid, input rnid, output resp, output data);

endinterface
