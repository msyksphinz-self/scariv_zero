// ------------------------------------------------------------------------
// NAME : scariv_phy_registers
// TYPE : module
// ------------------------------------------------------------------------
// Physical Registers
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_vec_registers
  import scariv_pkg::*;
#(
  parameter RD_PORT_SIZE = 10,
  parameter WR_PORT_SIZE = 5
)
(
  input logic i_clk,
  input logic i_reset_n,

  vec_regread_if.slave  regread  [RD_PORT_SIZE],
  vec_regwrite_if.slave regwrite [WR_PORT_SIZE]
);

localparam WIDTH = riscv_vec_conf_pkg::DLEN_W;

typedef logic [scariv_vec_pkg::VEC_RNID_W-1: 0] rnid_t;

logic [WIDTH-1: 0] r_phy_regs[scariv_vec_pkg::VEC_RNID_SIZE][scariv_vec_pkg::VEC_STEP_W];

logic [WR_PORT_SIZE-1:0]  wr_valid;
scariv_vec_pkg::vec_pos_t wr_pos [WR_PORT_SIZE];
rnid_t                    wr_rnid[WR_PORT_SIZE];
logic [WIDTH-1: 0]        wr_data[WR_PORT_SIZE];

generate for (genvar w_idx = 0; w_idx < WR_PORT_SIZE; w_idx++) begin : w_port_loop
  assign wr_valid[w_idx] = regwrite[w_idx].valid;
  assign wr_pos  [w_idx] = regwrite[w_idx].rd_pos;
  assign wr_rnid [w_idx] = regwrite[w_idx].rd_rnid;
  assign wr_data [w_idx] = regwrite[w_idx].rd_data;
end endgenerate


generate for (genvar r_idx = 0; r_idx < scariv_vec_pkg::VEC_RNID_SIZE; r_idx++) begin : reg_loop
  logic w_wr_valid;
  logic [WIDTH-1: 0]        w_wr_data;
  scariv_vec_pkg::vec_pos_t w_wr_pos;

  select_oh #(
      .SEL_WIDTH (WR_PORT_SIZE),
      .KEY_WIDTH (scariv_vec_pkg::VEC_RNID_W),
      .DATA_WIDTH(WIDTH)
  ) wr_data_select (
      .i_cmp_key (r_idx[scariv_vec_pkg::VEC_RNID_W-1:0]),
      .i_valid   (wr_valid),
      .i_keys    (wr_rnid),
      .i_data    (wr_data),
      .o_valid   (w_wr_valid),
      .o_data    (w_wr_data)
  );

  select_oh #(
      .SEL_WIDTH (WR_PORT_SIZE),
      .KEY_WIDTH (scariv_vec_pkg::VEC_RNID_W),
      .DATA_WIDTH($bits(scariv_vec_pkg::vec_pos_t))
  ) wr_pos_select (
      .i_cmp_key (r_idx[scariv_vec_pkg::VEC_RNID_W-1:0]),
      .i_valid   (wr_valid),
      .i_keys    (wr_rnid),
      .i_data    (wr_pos),
      .o_valid   (),
      .o_data    (w_wr_pos)
  );


  for (genvar s_idx = 0; s_idx < scariv_vec_pkg::VEC_STEP_W; s_idx++) begin : bank_loop

    always_ff @(posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_phy_regs[r_idx][s_idx] <= {WIDTH{1'b0}};
      end else begin
        if (w_wr_valid & (w_wr_pos == s_idx)) begin
          r_phy_regs[r_idx][s_idx] <= w_wr_data;
        end
      end
    end
  end // block: bank_loop

`ifdef SIMULATION
  logic [WIDTH-1: 0]  w_sim_phy_regs;
  assign w_sim_phy_regs = r_phy_regs[r_idx][0];
`endif // SIMULATION

end endgenerate // block: reg_loop

generate for (genvar p_idx = 0; p_idx < RD_PORT_SIZE; p_idx++) begin : port_loop
  assign regread[p_idx].data = r_phy_regs[regread[p_idx].rnid][regread[p_idx].pos];
end endgenerate

endmodule // scariv_vec_registers
