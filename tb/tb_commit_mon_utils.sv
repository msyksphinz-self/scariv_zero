logic [scariv_conf_pkg::CMT_ENTRY_SIZE-1: 0] rob_entries_valid;
scariv_pkg::rob_entry_t   rob_entries[scariv_conf_pkg::CMT_ENTRY_SIZE];
scariv_pkg::rob_entry_t   committed_rob_entry;
scariv_pkg::rob_payload_t committed_rob_payload;
generate for (genvar r_idx = 0; r_idx < scariv_conf_pkg::CMT_ENTRY_SIZE; r_idx++) begin : rob_loop
  assign rob_entries[r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.entry_loop[r_idx].u_entry.r_entry;
  assign rob_entries_valid[r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.entry_loop[r_idx].u_entry.r_entry.valid;
end endgenerate

logic [$clog2(scariv_conf_pkg::CMT_ENTRY_SIZE)-1: 0] w_commited_idx;
logic [scariv_conf_pkg::DISP_SIZE-1: 0]    w_dead_grp_id;
assign w_commited_idx = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_entry_id;
assign w_dead_grp_id = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_dead_grp_id;

assign committed_rob_entry   = rob_entries[w_commited_idx];
assign committed_rob_payload = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.u_payload_ram.data_array[w_commited_idx];

logic [riscv_pkg::XLEN_W-1: 0] w_physical_int_data [scariv_pkg::XPR_RNID_SIZE + 32];
logic [riscv_pkg::FLEN_W-1: 0] w_physical_fp_data  [scariv_pkg::FPR_RNID_SIZE + 32];
generate for (genvar r_idx = 0; r_idx < scariv_pkg::XPR_RNID_SIZE; r_idx++) begin: reg_loop
`ifdef NORMAL_MULTIPORT
  assign w_physical_int_data[r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_int_phy_registers.r_phy_regs[r_idx];
`else  // NORMAL_MULTIPORT
  assign w_physical_int_data[r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_int_phy_registers.sim_phy_regs[r_idx];
`endif // IVT_MULTIPORT
end endgenerate

generate if (riscv_pkg::FLEN_W != 0) begin
  for (genvar r_idx = 0; r_idx < scariv_pkg::FPR_RNID_SIZE; r_idx++) begin: reg_loop
`ifdef NORMAL_MULTIPORT
    assign w_physical_fp_data [r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.u_fp_phy_registers.r_phy_regs[r_idx];
`else // IVT_MULTIPORT
    assign w_physical_fp_data [r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.u_fp_phy_registers.sim_phy_regs[r_idx];
`endif // IVT_MULTIPORT
  end
end endgenerate

logic [11 : 0] r_timeout_counter;
logic          r_finish_valid;

always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
  if (!w_scariv_reset_n) begin
    r_timeout_counter <= 'h0;
    r_finish_valid <= 1'b0;
  end else begin
    if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_commit_if.commit_valid &
        (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_commit_if.payload.grp_id &
         ~u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.w_commit_if.payload.dead_id) != 'h0) begin
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
                  committed_rob_payload.disp[grp_idx].pc_addr << 1,
                  u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_entry_id,
                  1 << grp_idx,
                  committed_rob_payload.disp[grp_idx].inst,
                  committed_rob_payload.disp[grp_idx].inst);
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
