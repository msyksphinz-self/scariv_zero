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

logic [scariv_vec_pkg::VEC_RNID_SIZE-1: 0][WR_PORT_SIZE-1: 0] r_lvt;

generate for (genvar r_idx = 0; r_idx < RD_PORT_SIZE; r_idx++) begin : w_rd_loop
  logic [WIDTH-1: 0]  w_rd_data_d1[scariv_vec_pkg::VEC_STEP_W][WR_PORT_SIZE];
  for (genvar s_idx = 0; s_idx < scariv_vec_pkg::VEC_STEP_W; s_idx++) begin : step_loop
    for (genvar w_idx = 0; w_idx < WR_PORT_SIZE; w_idx++) begin : w_wr_loop
      wire  w_wr_valid = regwrite[w_idx].valid & (regwrite[w_idx].rd_pos == s_idx);

      data_array_2p
        #(
          .WIDTH (WIDTH ),
          .ADDR_W(scariv_vec_pkg::VEC_RNID_W)
          )
      u_array
        (
         .i_clk     (i_clk    ),
         .i_reset_n (i_reset_n),

         .i_wr      (w_wr_valid          ),
         .i_wr_addr (regwrite[w_idx].rd_rnid),
         .i_wr_data (regwrite[w_idx].rd_data),

         .i_rd_addr (regread[r_idx].rnid),
         .o_rd_data (w_rd_data_d1[s_idx][w_idx] )
         );

    end // block: w_wr_loop

  end // block: w_rd_loop

  logic [WR_PORT_SIZE-1: 0] r_lvt_d1;
  scariv_vec_pkg::vec_pos_t r_pos_d1;
  always_ff @ (posedge i_clk) begin
    r_lvt_d1 <= r_lvt[regread[r_idx].rnid];
    r_pos_d1 <= regread[r_idx].pos;
  end

  logic [WIDTH-1: 0] w_rd_data_sel;
  bit_oh_or #(.T(logic[WIDTH-1: 0]), .WORDS(WR_PORT_SIZE)) u_data_sel (.i_oh (r_lvt_d1), .i_data(w_rd_data_d1[r_pos_d1]), .o_selected(w_rd_data_sel));
  assign regread[r_idx].data = w_rd_data_sel;
end endgenerate // block: step_loop

generate for (genvar rn_idx = 0; rn_idx < scariv_vec_pkg::VEC_RNID_SIZE; rn_idx++) begin : rnid_loop
logic [WR_PORT_SIZE-1: 0] w_wr_valid;
  for (genvar w_idx = 0; w_idx < WR_PORT_SIZE; w_idx++) begin
    assign w_wr_valid[w_idx] = regwrite[w_idx].valid & (regwrite[w_idx].rd_rnid == rn_idx);
  end

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_lvt[rn_idx] <= 'h1;
    end else begin
      r_lvt[rn_idx] <= |w_wr_valid ? w_wr_valid : r_lvt[rn_idx];
    end
  end // always_ff @ (posedge i_clk, negedge i_reset_n)
end endgenerate // block: rnid_loop


`ifdef SIMULATION
logic [WIDTH-1: 0] sim_phy_regs[scariv_vec_pkg::VEC_RNID_SIZE];
generate for (genvar rn_idx = 0; rn_idx < scariv_vec_pkg::VEC_RNID_SIZE; rn_idx++) begin : sim_rn_loop
logic [WIDTH-1: 0] sim_phy_rn_data[WR_PORT_SIZE];
  for (genvar wr_idx = 0; wr_idx < WR_PORT_SIZE; wr_idx++) begin
    assign sim_phy_rn_data[wr_idx] = w_rd_loop[0].step_loop[0].w_wr_loop[wr_idx].u_array.data_array[rn_idx];
  end
  bit_oh_or #(.T(logic[WIDTH-1: 0]), .WORDS(WR_PORT_SIZE)) u_data_sel (.i_oh (r_lvt[rn_idx]), .i_data(sim_phy_rn_data), .o_selected(sim_phy_regs[rn_idx]));
end endgenerate

`endif // SIMULATION

endmodule // scariv_vec_registers
