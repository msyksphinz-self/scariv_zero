logic [scariv_conf_pkg::CMT_ENTRY_SIZE-1: 0] rob_entries_valid;
scariv_pkg::rob_entry_t rob_entries[scariv_conf_pkg::CMT_ENTRY_SIZE];
scariv_pkg::rob_entry_t committed_rob_entry;
generate for (genvar r_idx = 0; r_idx < scariv_conf_pkg::CMT_ENTRY_SIZE; r_idx++) begin : rob_loop
  assign rob_entries[r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.entry_loop[r_idx].u_entry.r_entry;
  assign rob_entries_valid[r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.entry_loop[r_idx].u_entry.r_entry.valid;
end
endgenerate

logic [scariv_conf_pkg::CMT_ENTRY_SIZE-1: 0] w_commited_oh;
logic [scariv_conf_pkg::DISP_SIZE-1: 0]    w_dead_grp_id;
assign w_commited_oh = 'h1 << u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_entry_id;
assign w_dead_grp_id = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_dead_grp_id;

bit_oh_or
  #(
    .T(scariv_pkg::rob_entry_t),
    .WORDS(scariv_conf_pkg::CMT_ENTRY_SIZE)
    )
committed_entry
  (
   .i_oh(w_commited_oh),
   .i_data(rob_entries),
   .o_selected(committed_rob_entry)
);


logic [riscv_pkg::XLEN_W-1: 0] w_physical_int_data [scariv_pkg::XPR_RNID_SIZE + 32];
logic [riscv_pkg::FLEN_W-1: 0] w_physical_fp_data  [scariv_pkg::FPR_RNID_SIZE + 32];
generate for (genvar r_idx = 0; r_idx < scariv_pkg::XPR_RNID_SIZE; r_idx++) begin: reg_loop
  assign w_physical_int_data[r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_int_phy_registers.r_phy_regs[r_idx];
end endgenerate

generate if (riscv_pkg::FLEN_W != 0) begin
  for (genvar r_idx = 0; r_idx < scariv_pkg::FPR_RNID_SIZE; r_idx++) begin: reg_loop
    assign w_physical_fp_data [r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.u_fp_phy_registers.r_phy_regs[r_idx];
  end
end endgenerate

logic [riscv_vec_conf_pkg::VLEN_W-1: 0] w_physical_vec_data [scariv_vec_pkg::VEC_RNID_SIZE + 32];
generate if (riscv_vec_conf_pkg::VLEN_W != 0) begin
  for (genvar r_idx = 0; r_idx < scariv_vec_pkg::VEC_RNID_SIZE; r_idx++) begin: reg_loop
    for (genvar step_idx = 0; step_idx < scariv_vec_pkg::VEC_STEP_W; step_idx++) begin
      assign w_physical_vec_data [r_idx][step_idx * riscv_vec_conf_pkg::DLEN_W +: riscv_vec_conf_pkg::DLEN_W] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.vpu.u_vec_registers.r_phy_regs[step_idx][r_idx];
    end
  end
end endgenerate

logic [11 : 0] r_timeout_counter;
logic          r_finish_valid;

always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
  if (!w_scariv_reset_n) begin
    r_timeout_counter <= 'h0;
    r_finish_valid <= 1'b0;
  end else begin
    if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.o_commit.commit &
        (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.o_commit.grp_id &
         ~u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.o_commit.dead_id) != 'h0) begin
      r_timeout_counter <= 'h0;
    end else begin
      r_timeout_counter <= r_timeout_counter + 'h1;
    end
    if (&r_timeout_counter) begin
      $display("FATAL : COMMIT DEADLOCKED\n");
      for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++) begin
        if (rob_entries_valid[u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_id[scariv_pkg::CMT_ENTRY_W-1: 0]] &
            rob_entries[u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_id[scariv_pkg::CMT_ENTRY_W-1: 0]].grp_id[grp_idx] &
            !rob_entries[u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_id[scariv_pkg::CMT_ENTRY_W-1: 0]].done_grp_id[grp_idx]) begin
          $write ("DEADLOCKED : %t PC=%010x (%02d,%02d) %08x DASM(%08x)\n",
                  $time,
                  /* verilator lint_off WIDTH */
                  (committed_rob_entry.pc_addr << 1) + (4 * grp_idx),
                  u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_entry_id,
                  1 << grp_idx,
                  rob_entries[u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_id].inst[grp_idx].inst,
                  rob_entries[u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_id].inst[grp_idx].inst);
        end // if (rob_entries[u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_id].valid &...
      end // for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++)
      step_spike_wo_cmp(10);
      stop_sim_deadlock($time / 4);
      r_finish_valid <= 1'b1;
    end
  end
end

always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
  if (!w_scariv_reset_n) begin
  end else begin
    if (r_finish_valid) begin
      $finish;
    end
  end
end
