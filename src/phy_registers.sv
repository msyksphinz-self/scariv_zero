module mrh_phy_registers #(
    parameter RD_PORT_SIZE = 10
) (
    input logic i_clk,
    input logic i_reset_n,

          regread_if.slave  regread  [         RD_PORT_SIZE],
    input mrh_pkg::target_t target_in[mrh_pkg::TGT_BUS_SIZE]
);

  logic [riscv_pkg::XLEN_W-1:0] r_phy_regs[mrh_pkg::RNID_SIZE];

  logic [mrh_pkg::TGT_BUS_SIZE-1:0] wr_valid;
  logic [mrh_pkg::RNID_W-1:0] wr_rnid[mrh_pkg::TGT_BUS_SIZE];
  logic [riscv_pkg::XLEN_W-1:0] wr_data[mrh_pkg::TGT_BUS_SIZE];

  generate
    for (genvar w_idx = 0; w_idx < mrh_pkg::TGT_BUS_SIZE; w_idx++) begin : w_port_loop
      assign wr_valid[w_idx] = target_in[w_idx].valid;
      assign wr_rnid [w_idx] = target_in[w_idx].rd_rnid;
      assign wr_data [w_idx] = target_in[w_idx].rd_data;
    end
  endgenerate

  generate
    for (genvar r_idx = 0; r_idx < mrh_pkg::RNID_SIZE; r_idx++) begin : reg_loop
      logic w_wr_valid;
      logic [riscv_pkg::XLEN_W-1:0] w_wr_data;
      select_oh #(
          .SEL_WIDTH (mrh_pkg::TGT_BUS_SIZE),
          .KEY_WIDTH (mrh_pkg::RNID_W),
          .DATA_WIDTH(riscv_pkg::XLEN_W)
      ) wr_data_select (
          .i_cmp_key(r_idx),
          .i_valid(wr_valid),
          .i_keys(wr_rnid),
          .i_data(wr_data),
          .o_valid(w_wr_valid),
          .o_data(w_wr_data)
      );
      always_ff @(posedge i_clk, negedge i_reset_n) begin
        if (!i_reset_n) begin
          r_phy_regs[r_idx] <= {riscv_pkg::XLEN_W{1'b0}};
        end else begin
          if (w_wr_valid) begin
            r_phy_regs[r_idx] <= w_wr_data;
          end
        end
      end
    end
  endgenerate

  generate
    for (genvar p_idx = 0; p_idx < RD_PORT_SIZE; p_idx++) begin : port_loop

      always_ff @(posedge i_clk, negedge i_reset_n) begin
        if (!i_reset_n) begin
          regread[p_idx].resp <= 1'b0;
        end else begin
          regread[p_idx].resp <= regread[p_idx].valid;
          regread[p_idx].data <= r_phy_regs[regread[p_idx].rnid];
        end
      end
    end
  endgenerate

endmodule
