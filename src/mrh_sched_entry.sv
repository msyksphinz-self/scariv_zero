module mrh_sched_entry
  #(
    parameter REL_BUS_SIZE = 10
    )
(
   input logic i_clk,
   input logic i_reset_n,

   input logic            i_put,
   input mrh_pkg::disp_t  i_put_data,

   output logic           o_entry_ready,
   output mrh_pkg::disp_t o_entry,

   /* Forwarding path */
   input mrh_pkg::release_t release_in[REL_BUS_SIZE]
   );


mrh_pkg::disp_t r_entry;
mrh_pkg::disp_t r_entry_d;

logic [REL_BUS_SIZE-1: 0] w_rs1_rel_fwd_valid;
logic [REL_BUS_SIZE-1: 0] w_rs2_rel_fwd_valid;

generate for (genvar rs_idx = 0; rs_idx < REL_BUS_SIZE; rs_idx++) begin : rs_rel_loop
  assign w_rs1_rel_fwd_valid[i] = r_entry.rs1_valid & release_in[rs_idx].rd_valid &
                                  (r_entry.rs1_type == release_in[rs_idx].rd_type) &
                                  (r_entry.rs1_rnid == release_in[rs_idx].rd_rnid);

  assign w_rs2_rel_fwd_valid[i] = r_entry.rs2_valid & release_in[rs_idx].rd_valid &
                                  (r_entry.rs2_type == release_in[rs_idx].rd_type) &
                                  (r_entry.rs2_rnid == release_in[rs_idx].rd_rnid);
end
endgenerate

always_comb begin
  r_entry_d = i_put ? i_put_data : r_entry;

  if (r_entry.rs1_valid & !r_entry.rs1_ready & |w_rs1_rel_fwd_valid) begin
    r_entry_d.rs1_ready = 1'b1;
  end

  if (r_entry.rs2_valid & !r_entry.rs2_ready & |w_rs2_rel_fwd_valid) begin
    r_entry_d.rs2_ready = 1'b1;
  end
end


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_entry <= 'h0;
  end else begin
    r_entry <= r_entry_d;
  end
end

assign o_entry_ready = r_entry.valid &
                       (r_entry.rs1_valid & r_entry.rs1_ready | !r_entry.rs1_valid) &
                       (r_entry.rs2_valid & r_entry.rs2_ready | !r_entry.rs2_valid);


endmodule // mrh_sched_entry
