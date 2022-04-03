module msrh_phy_registers
  import msrh_pkg::*;
#(
  parameter REG_TYPE = GPR,
  parameter RD_PORT_SIZE = 10
)
(
    input logic i_clk,
    input logic i_reset_n,

    regread_if.slave         regread [          RD_PORT_SIZE],
    input msrh_pkg::phy_wr_t i_phy_wr[msrh_pkg::TGT_BUS_SIZE]
);

localparam WIDTH = REG_TYPE == GPR ? riscv_pkg::XLEN_W : riscv_pkg::FLEN_W;

  logic [WIDTH-1: 0] r_phy_regs[msrh_pkg::RNID_SIZE];

  logic [msrh_pkg::TGT_BUS_SIZE-1:0] wr_valid;
  msrh_pkg::rnid_t wr_rnid[msrh_pkg::TGT_BUS_SIZE];
  logic [WIDTH-1: 0] wr_data[msrh_pkg::TGT_BUS_SIZE];

generate for (genvar w_idx = 0; w_idx < msrh_pkg::TGT_BUS_SIZE; w_idx++) begin : w_port_loop
  assign wr_valid[w_idx] = i_phy_wr[w_idx].valid & (i_phy_wr[w_idx].rd_type == REG_TYPE);
  assign wr_rnid [w_idx] = i_phy_wr[w_idx].rd_rnid;
  assign wr_data [w_idx] = i_phy_wr[w_idx].rd_data;
end
endgenerate

// RNID = 0 is always for X0

generate for (genvar r_idx = 0; r_idx < msrh_pkg::RNID_SIZE; r_idx++) begin : reg_loop
  if ((REG_TYPE == GPR) & (r_idx == 0)) begin
    assign r_phy_regs[r_idx] = {riscv_pkg::XLEN_W{1'b0}};
  end else begin
    logic w_wr_valid;
    logic [WIDTH-1: 0]  w_wr_data;
    select_oh #(
        .SEL_WIDTH (msrh_pkg::TGT_BUS_SIZE),
        .KEY_WIDTH (msrh_pkg::RNID_W),
        .DATA_WIDTH(WIDTH)
    ) wr_data_select (
        .i_cmp_key(r_idx[msrh_pkg::RNID_W-1:0]),
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

  generate
    for (genvar p_idx = 0; p_idx < RD_PORT_SIZE; p_idx++) begin : port_loop

      logic w_wr_valid;
      logic [WIDTH-1: 0] w_wr_data;

      select_oh #(
          .SEL_WIDTH (msrh_pkg::TGT_BUS_SIZE),
          .KEY_WIDTH (msrh_pkg::RNID_W),
          .DATA_WIDTH(WIDTH)
      ) wr_data_fwd (
          .i_cmp_key(regread[p_idx].rnid),
          .i_valid(wr_valid),
          .i_keys(wr_rnid),
          .i_data(wr_data),
          .o_valid(w_wr_valid),
          .o_data(w_wr_data)
      );

      always_comb begin
        regread[p_idx].resp = regread[p_idx].valid;
        regread[p_idx].data = (REG_TYPE == GPR) & regread[p_idx].rnid == 'h0 ? 'h0       :
                              w_wr_valid                 ? w_wr_data :
                              r_phy_regs[regread[p_idx].rnid];
      end
    end
  endgenerate


endmodule
