// ------------------------------------------------------------------------
// NAME : scariv_phy_registers
// TYPE : module
// ------------------------------------------------------------------------
// Physical Registers
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_phy_registers
  import scariv_pkg::*;
#(
  parameter REG_TYPE = GPR,
  parameter RD_PORT_SIZE = 10,
  parameter WR_PORT_SIZE = 5,
  localparam RNID_SIZE  = REG_TYPE == GPR ? XPR_RNID_SIZE  : FPR_RNID_SIZE,
  localparam RNID_W = $clog2(RNID_SIZE),
  localparam type rnid_t = logic [RNID_W-1: 0])
(
    input logic i_clk,
    input logic i_reset_n,

    regread_if.slave         regread  [RD_PORT_SIZE],
    regwrite_if.slave        regwrite [WR_PORT_SIZE]
);

localparam WIDTH = REG_TYPE == GPR ? riscv_pkg::XLEN_W : riscv_fpu_pkg::FLEN_W;

  logic [WIDTH-1: 0] r_phy_regs[RNID_SIZE];

  logic [WR_PORT_SIZE-1:0] wr_valid;
  rnid_t wr_rnid[WR_PORT_SIZE];
  logic [WIDTH-1: 0] wr_data[WR_PORT_SIZE];

generate for (genvar w_idx = 0; w_idx < WR_PORT_SIZE; w_idx++) begin : w_port_loop
  assign wr_valid[w_idx] = regwrite[w_idx].valid;
  assign wr_rnid [w_idx] = regwrite[w_idx].rnid;
  assign wr_data [w_idx] = regwrite[w_idx].data;
end
endgenerate

// RNID = 0 is always for X0

generate for (genvar r_idx = 0; r_idx < RNID_SIZE; r_idx++) begin : reg_loop
  if ((REG_TYPE == GPR) & (r_idx == 0)) begin
    assign r_phy_regs[r_idx] = {riscv_pkg::XLEN_W{1'b0}};
  end else begin
    logic w_wr_valid;
    logic [WIDTH-1: 0]  w_wr_data;
    select_oh #(
        .SEL_WIDTH (WR_PORT_SIZE),
        .KEY_WIDTH (RNID_W),
        .DATA_WIDTH(WIDTH)
    ) wr_data_select (
        .i_cmp_key(r_idx[RNID_W-1:0]),
        .i_valid(wr_valid),
        .i_keys(wr_rnid),
        .i_data(wr_data),
        .o_valid(w_wr_valid),
        .o_data(w_wr_data)
    );
    always_ff @(posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_phy_regs[r_idx] <= {WIDTH{1'b0}};
      end else begin
        if (w_wr_valid) begin
          r_phy_regs[r_idx] <= w_wr_data;
        end
      end
    end
  end // else: !if((REG_TYPE == GPR) & (r_idx == 0))
`ifdef SIMULATION
  logic [WIDTH-1: 0]  w_sim_phy_regs;
  assign w_sim_phy_regs = r_phy_regs[r_idx];
`endif // SIMULATION
end
endgenerate

generate for (genvar p_idx = 0; p_idx < RD_PORT_SIZE; p_idx++) begin : port_loop
  always_comb begin
    regread[p_idx].resp = regread[p_idx].valid;
    regread[p_idx].data = (REG_TYPE == GPR) & regread[p_idx].rnid == 'h0 ? 'h0       :
                          r_phy_regs[regread[p_idx].rnid];
  end
end endgenerate


endmodule
