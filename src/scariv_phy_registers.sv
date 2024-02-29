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

// `define USE_DISTRIBUTED_RAM
`define USE_BLOCK_RAM
// `define USE_NORMAL_MULTIPORT

`ifdef USE_DISTRIBUTED_RAM

logic [WR_PORT_SIZE-1: 0] w_wr_valid;
logic [RNID_W-1: 0]       w_wr_addr[WR_PORT_SIZE];
logic [WIDTH-1: 0]        w_wr_data[WR_PORT_SIZE];

generate for (genvar w_idx = 0; w_idx < WR_PORT_SIZE; w_idx++) begin : wr_loop
  assign w_wr_valid[w_idx] = regwrite[w_idx].valid;
  assign w_wr_addr [w_idx] = regwrite[w_idx].rnid;
  assign w_wr_data [w_idx] = regwrite[w_idx].data;
end endgenerate

logic [RNID_W-1: 0]       w_rd_addr[RD_PORT_SIZE];
logic [WIDTH-1: 0]        w_rd_data[RD_PORT_SIZE];

generate for (genvar r_idx = 0; r_idx < RD_PORT_SIZE; r_idx++) begin : rd_loop
  always_ff @ (posedge i_clk) begin
    if ((REG_TYPE == GPR) & (regread[r_idx].rnid == 'h0)) begin
      regread[r_idx].data <= 'h0;
    end else begin
      regread[r_idx].data <= w_rd_data[r_idx];
    end
  end
  assign w_rd_addr[r_idx] = regread[r_idx].rnid;
end endgenerate

distributed_mp_ram
  #(
    .WR_PORTS (WR_PORT_SIZE),
    .RD_PORTS (RD_PORT_SIZE),
    .WIDTH (WIDTH ),
    .WORDS (RNID_SIZE)
    )
u_array
 (
  .i_clk     (i_clk    ),
  .i_reset_n (i_reset_n),

  .i_wr      (w_wr_valid),
  .i_wr_addr (w_wr_addr ),
  .i_wr_data (w_wr_data ),

  .i_rd_addr (w_rd_addr),
  .o_rd_data (w_rd_data)
  );

`ifdef SIMULATION
  logic [WIDTH-1: 0] sim_phy_regs[RNID_SIZE];
  generate for (genvar rn_idx = 0; rn_idx < RNID_SIZE; rn_idx++) begin : sim_rn_loop
    logic [WIDTH-1: 0] sim_phy_rn_data[WR_PORT_SIZE];
    for (genvar wr_idx = 0; wr_idx < WR_PORT_SIZE; wr_idx++) begin
      assign sim_phy_rn_data[wr_idx] = u_array.w_rd_loop[0].w_wr_loop[wr_idx].data_array[rn_idx];
    end
    bit_oh_or #(.T(logic[WIDTH-1: 0]), .WORDS(WR_PORT_SIZE)) u_data_sel (.i_oh (u_array.r_lvt[rn_idx]), .i_data(sim_phy_rn_data), .o_selected(sim_phy_regs[rn_idx]));
  end endgenerate
`endif // SIMULATION

`endif //  `ifdef USE_DISTRIBUTED_RAM

`ifdef USE_BLOCK_RAM

// USE BLOCK RAM

logic [RNID_SIZE-1: 0][WR_PORT_SIZE-1: 0] r_lvt;

generate for (genvar r_idx = 0; r_idx < RD_PORT_SIZE; r_idx++) begin : w_rd_loop
  logic [WIDTH-1: 0]  w_rd_data_d1[WR_PORT_SIZE];

  for (genvar w_idx = 0; w_idx < WR_PORT_SIZE; w_idx++) begin : w_wr_loop

    logic w_wr_valid;
    if (REG_TYPE == GPR) begin
      assign w_wr_valid = regwrite[w_idx].valid & (regwrite[w_idx].rnid != 'h0);
    end else begin
      assign w_wr_valid = regwrite[w_idx].valid;
    end

    data_array_2p
      #(
        .WIDTH (WIDTH ),
        .ADDR_W(RNID_W)
        )
    u_array
     (
      .i_clk     (i_clk    ),
      .i_reset_n (i_reset_n),

      .i_wr      (w_wr_valid          ),
      .i_wr_addr (regwrite[w_idx].rnid),
      .i_wr_data (regwrite[w_idx].data),

      .i_rd_addr (regread[r_idx].rnid),
      .o_rd_data (w_rd_data_d1[w_idx] )
      );

  end // block: w_wr_loop


  logic [WR_PORT_SIZE-1: 0] r_lvt_d1;
  logic                     r_rnid_zero;
  always_ff @ (posedge i_clk) begin
    r_lvt_d1    <= r_lvt[regread[r_idx].rnid];
    r_rnid_zero <= regread[r_idx].rnid == 'h0;
  end

  logic [WIDTH-1: 0] w_rd_data_sel;
  bit_oh_or #(.T(logic[WIDTH-1: 0]), .WORDS(WR_PORT_SIZE)) u_data_sel (.i_oh (r_lvt_d1), .i_data(w_rd_data_d1), .o_selected(w_rd_data_sel));
  assign regread[r_idx].data = REG_TYPE == GPR & r_rnid_zero ? 'h0 : w_rd_data_sel;
end endgenerate // block: w_rd_loop

generate for (genvar rn_idx = 0; rn_idx < RNID_SIZE; rn_idx++) begin : rnid_loop
  logic [WR_PORT_SIZE-1: 0] w_wr_valid;
  for (genvar w_idx = 0; w_idx < WR_PORT_SIZE; w_idx++) begin
    assign w_wr_valid[w_idx] = regwrite[w_idx].valid & (regwrite[w_idx].rnid == rn_idx);
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
logic [WIDTH-1: 0] sim_phy_regs[RNID_SIZE];
generate for (genvar rn_idx = 0; rn_idx < RNID_SIZE; rn_idx++) begin : sim_rn_loop
logic [WIDTH-1: 0] sim_phy_rn_data[WR_PORT_SIZE];
  for (genvar wr_idx = 0; wr_idx < WR_PORT_SIZE; wr_idx++) begin
    assign sim_phy_rn_data[wr_idx] = w_rd_loop[0].w_wr_loop[wr_idx].u_array.data_array[rn_idx];
  end
  bit_oh_or #(.T(logic[WIDTH-1: 0]), .WORDS(WR_PORT_SIZE)) u_data_sel (.i_oh (r_lvt[rn_idx]), .i_data(sim_phy_rn_data), .o_selected(sim_phy_regs[rn_idx]));
end endgenerate

`endif // SIMULATION

`endif //  `ifdef USE_BLOCK_RAM

`ifdef USE_NORMAL_MULTIPORT

logic [WIDTH-1: 0] r_phy_regs[RNID_SIZE];

logic [WR_PORT_SIZE-1:0] wr_valid;
rnid_t                   wr_rnid[WR_PORT_SIZE];
logic [WIDTH-1: 0]       wr_data[WR_PORT_SIZE];

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
  // always_comb begin
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      regread[p_idx].resp <= 1'b0;
    end else begin
      regread[p_idx].resp <= regread[p_idx].valid;
      regread[p_idx].data <= (REG_TYPE == GPR) & regread[p_idx].rnid == 'h0 ? 'h0 :
                             r_phy_regs[regread[p_idx].rnid];
    end
  end
end endgenerate

`endif //  `ifdef USE_NORMAL_MULTIPORT

endmodule
