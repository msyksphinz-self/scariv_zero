module select_phy_wr_data
  #(parameter BUS_SIZE = scariv_pkg::TGT_BUS_SIZE)
(
   input scariv_pkg::rnid_t   i_entry_rnid,
   input scariv_pkg::reg_t    i_entry_type,
   phy_wr_if.slave            phy_wr_if[BUS_SIZE],

   output logic               o_valid,
   output scariv_pkg::alen_t  o_data
   );

logic [BUS_SIZE-1:0] w_hit;
scariv_pkg::alen_t     w_data[BUS_SIZE];
//
generate for (genvar r_idx = 0; r_idx < BUS_SIZE; r_idx++) begin : phy_wr_loop
  assign w_hit[r_idx] = phy_wr_if[r_idx].valid &&
                        ((phy_wr_if[r_idx].rd_type == scariv_pkg::GPR) ? (phy_wr_if[r_idx].rd_rnid != 'h0) : 1'b1) &
                        (i_entry_rnid == phy_wr_if[r_idx].rd_rnid) &&
                        (i_entry_type == phy_wr_if[r_idx].rd_type);
  assign w_data[r_idx] = phy_wr_if[r_idx].rd_data;
end endgenerate
//
assign o_valid = |w_hit;
// bit_oh_or #(.T(scariv_pkg::alen_t), .WORDS(BUS_SIZE))
// u_data_select(.i_oh(w_hit), .i_data(w_data), .o_selected(o_data));

function automatic scariv_pkg::alen_t bit_select();
  for (int i = 0; i < BUS_SIZE; i++) begin
    if (w_hit[i]) return w_data[i];
  end
  return 0;
endfunction // bit_oh_func
assign o_data = bit_select();

endmodule // select_phy_wr_data
