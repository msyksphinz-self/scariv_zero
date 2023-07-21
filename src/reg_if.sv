interface regread_if #(parameter REG_TYPE = scariv_pkg::GPR);

  localparam WDITH_W = REG_TYPE == scariv_pkg::GPR ? riscv_pkg::XLEN_W : riscv_fpu_pkg::FLEN_W;

  logic                valid;
  scariv_pkg::rnid_t   rnid;
  logic                resp;
  logic [WDITH_W-1: 0] data;

  modport master(output valid, output rnid, input resp, input data);

  modport slave(input valid, input rnid, output resp, output data);

endinterface

interface regwrite_if #(parameter REG_TYPE = scariv_pkg::GPR);
  localparam WDITH_W = REG_TYPE == scariv_pkg::GPR ? riscv_pkg::XLEN_W : riscv_fpu_pkg::FLEN_W;

  logic                valid;
  scariv_pkg::rnid_t   rnid;
  logic [WDITH_W-1: 0] data;

  modport master(output valid, output rnid, output data);
  modport slave (input valid,  input rnid,  input data);

endinterface
