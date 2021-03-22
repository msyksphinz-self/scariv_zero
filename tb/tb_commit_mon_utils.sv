msrh_pkg::rob_entry_t rob_entries[msrh_pkg::CMT_BLK_SIZE];
msrh_pkg::rob_entry_t committed_rob_entry;
generate for (genvar r_idx = 0; r_idx < msrh_pkg::CMT_BLK_SIZE; r_idx++) begin : rob_loop
  assign rob_entries[r_idx] = u_msrh_tile_wrapper.u_msrh_tile.u_rob.entry_loop[r_idx].u_entry.r_entry;
end
endgenerate

logic [msrh_pkg::CMT_BLK_SIZE-1: 0] w_commited_oh;
logic [msrh_pkg::DISP_SIZE-1: 0]    w_dead_grp_id;
assign w_commited_oh = 'h1 << u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id;
assign w_dead_grp_id = u_msrh_tile_wrapper.u_msrh_tile.u_rob.r_killing_uncmts &
                       (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_in_cmt_id != u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id) ?
                       committed_rob_entry.grp_id :
                       u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_dead_grp_id;

bit_oh_or
  #(
    .WIDTH($size(msrh_pkg::rob_entry_t)),
    .WORDS(msrh_pkg::CMT_BLK_SIZE)
    )
commite_entry
  (
   .i_oh(w_commited_oh),
   .i_data(rob_entries),
   .o_selected(committed_rob_entry)
);


logic [riscv_pkg::XLEN_W-1: 0] w_physical_gpr_data [msrh_pkg::RNID_SIZE + 32];
generate for (genvar r_idx = 0; r_idx < msrh_pkg::RNID_SIZE; r_idx++) begin: reg_loop
  assign w_physical_gpr_data[r_idx] = u_msrh_tile_wrapper.u_msrh_tile.u_int_phy_registers.r_phy_regs[r_idx];
end
endgenerate
