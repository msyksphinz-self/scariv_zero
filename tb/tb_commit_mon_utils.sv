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


logic [riscv_pkg::XLEN_W-1: 0] w_physical_int_data [scariv_pkg::RNID_SIZE + 32];
logic [riscv_pkg::FLEN_W-1: 0] w_physical_fp_data  [scariv_pkg::RNID_SIZE + 32];
generate for (genvar r_idx = 0; r_idx < scariv_pkg::RNID_SIZE; r_idx++) begin: reg_loop
  assign w_physical_int_data[r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_int_phy_registers.r_phy_regs[r_idx];
  if (riscv_pkg::FLEN_W != 0) begin
    assign w_physical_fp_data [r_idx] = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.u_fp_phy_registers.r_phy_regs[r_idx];
  end
end
endgenerate

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

// always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
//   if (!w_scariv_reset_n) begin
//   end else begin
//     if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_scariv_lsu_top.w_l1d_wr_if.valid &
//         (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_scariv_lsu_top.w_l1d_wr_if.paddr == 'h8000_1000) |
//         (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_scariv_lsu_top.w_l1d_wr_if.paddr == 'h8000_3000)) begin
//       $write("===============================\n");
//       $write("SIMULATION FINISH : ");
//       if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_scariv_lsu_top.w_l1d_wr_if.data[31: 0] == 32'h1) begin
//         $write("PASS\n");
//       end else begin
//         $write("FAIL(%x)\n", u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_scariv_lsu_top.w_l1d_wr_if.data[31: 0]);
//       end
//       $write("===============================\n");
//       $finish;
//     end
//   end // else: !if(!w_scariv_reset_n)
// end // always_ff @ (negedge w_clk, negedge w_scariv_reset_n)

// ==========================
// FreeList Checker
// ==========================

// logic [scariv_pkg::RNID_W-1: 0] rename_map_model[32];
int rename_map_model[32];

initial begin
  for(int i = 0; i < 32; i++) begin
    rename_map_model[i] = i;
  end
end


logic [scariv_pkg::FLIST_SIZE-1:0][scariv_pkg::RNID_W-1: 0] freelist_model[5];

initial begin
  for (int d = 0; d < 5; d++) begin
    for (int i = 0; i < 32; i++) begin
      /* verilator lint_off WIDTH */
      freelist_model[d][i] = 32 + d * scariv_pkg::FLIST_SIZE + i;
    end
  end
end

// always @ (negedge w_clk, negedge w_scariv_reset_n) begin
//   if (w_scariv_reset_n) begin
//     if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_valid) begin
//       for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++) begin
//         if (committed_rob_entry.grp_id[grp_idx] & !w_dead_grp_id[grp_idx]) begin
//           if (committed_rob_entry.inst[grp_idx].rd_valid &&
//               (committed_rob_entry.inst[grp_idx].rd_regidx != 0)) begin
//           logic [scariv_pkg::RNID_W-1: 0] poped_rnid;
//             poped_rnid = freelist_model[grp_idx][0];
//             for(int i = 0; i < scariv_pkg::FLIST_SIZE-1; i++) begin
//               freelist_model[grp_idx][i] = freelist_model[grp_idx][i+1];
//             end
//             freelist_model[grp_idx][scariv_pkg::FLIST_SIZE-1] = committed_rob_entry.inst[grp_idx].rd_old_rnid;
//
//             if (rename_map_model[committed_rob_entry.inst[grp_idx].rd_regidx] !=
//                 committed_rob_entry.inst[grp_idx].rd_old_rnid) begin
//               $fatal(0, "Error: Returned rnid different %d != %d",
//                      rename_map_model[committed_rob_entry.inst[grp_idx].rd_regidx],
//                      committed_rob_entry.inst[grp_idx].rd_old_rnid);
//
//             end
//
//             if (poped_rnid != committed_rob_entry.inst[grp_idx].rd_rnid) begin
//               $fatal(0, "Error: (%02d, %02d) Destination rnid different %d != %d",
//                      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_cmt_id,
//                      1 << grp_idx,
//                      poped_rnid,
//                      committed_rob_entry.inst[grp_idx].rd_rnid);
//             end
//
//             rename_map_model[committed_rob_entry.inst[grp_idx].rd_regidx] <= poped_rnid;
//           end // if (committed_rob_entry.inst[grp_idx].rd_valid)
//         end // if (committed_rob_entry.grp_id[grp_idx] & !w_dead_grp_id[grp_idx])
//       end // for (int grp_idx = 0; grp_idx < scariv_conf_pkg::DISP_SIZE; grp_idx++)
//     end // if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.w_out_valid)
//   end // if (i_reset_n)
// end // always_ff @ (negedge i_clk, negedge i_reset_n)
