module msrh_rob_entry
  (
   input logic i_clk,
   input logic i_reset_n,

   input logic i_load_valid,
   input logic [msrh_pkg::DISP_SIZE-1:0] i_old_rd_valid,
   input logic [msrh_pkg::RNID_W-1:0]    i_old_rd_rnid[msrh_pkg::DISP_SIZE]
   );

logic                                    r_valid;
logic [msrh_pkg::DISP_SIZE-1:0]          r_old_rd_valid;
logic [msrh_pkg::RNID_W-1:0]             r_old_rd_rnid[msrh_pkg::DISP_SIZE];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_valid <= 1'b0;
  end else begin
    if (i_load_valid) begin
      for (int i = 0; i < msrh_pkg::DISP_SIZE; i++) begin
        r_old_rd_valid[i] <= i_old_rd_valid[i];
        r_old_rd_rnid [i] <= i_old_rd_rnid [i];
      end
    end
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)


endmodule // msrh_rob_entry
