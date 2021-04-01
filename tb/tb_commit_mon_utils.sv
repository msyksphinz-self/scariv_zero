int log_fp;
int pipe_fp;
initial begin
  log_fp = $fopen("simulate.log");
  pipe_fp = $fopen("pipetrace.log");
end

logic [msrh_pkg::CMT_BLK_SIZE-1: 0] rob_entries_valid;
msrh_pkg::rob_entry_t rob_entries[msrh_pkg::CMT_BLK_SIZE];
msrh_pkg::rob_entry_t committed_rob_entry;
generate for (genvar r_idx = 0; r_idx < msrh_pkg::CMT_BLK_SIZE; r_idx++) begin : rob_loop
  assign rob_entries[r_idx] = u_msrh_tile_wrapper.u_msrh_tile.u_rob.entry_loop[r_idx].u_entry.r_entry;
  assign rob_entries_valid[r_idx] = u_msrh_tile_wrapper.u_msrh_tile.u_rob.entry_loop[r_idx].u_entry.r_valid;
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
    .T(msrh_pkg::rob_entry_t),
    .WORDS(msrh_pkg::CMT_BLK_SIZE)
    )
committed_entry
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

logic [ 8 : 0] r_timeout_counter;

always_ff @ (negedge w_clk, negedge w_msrh_reset_n) begin
  if (!w_msrh_reset_n) begin
    r_timeout_counter <= 'h0;
  end else begin
    if (u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_vld) begin
      r_timeout_counter <= 'h0;
    end else begin
      r_timeout_counter <= r_timeout_counter + 'h1;
    end
    if (&r_timeout_counter) begin
      $display("FATAL : COMMIT DEADLOCKED\n");
      for (int grp_idx = 0; grp_idx < msrh_pkg::DISP_SIZE; grp_idx++) begin
        if (rob_entries_valid[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id] &
            rob_entries[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id].grp_id[grp_idx] &
            !rob_entries[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id].done_grp_id[grp_idx]) begin
          $write ("DEADLOCKED : %t PC=%010x (%02d,%02d) %08x DASM(%08x)\n",
                  $time,
                  /* verilator lint_off WIDTH */
                  (committed_rob_entry.pc_addr << 1) + (4 * grp_idx),
                  u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id,
                  1 << grp_idx,
                  rob_entries[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id].inst[grp_idx].inst,
                  rob_entries[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id].inst[grp_idx].inst);
        end // if (rob_entries[u_msrh_tile_wrapper.u_msrh_tile.u_rob.w_out_cmt_id].valid &...
      end // for (int grp_idx = 0; grp_idx < msrh_pkg::DISP_SIZE; grp_idx++)
      $fatal;
    end
  end
end

always_ff @ (negedge w_clk, negedge w_msrh_reset_n) begin
  if (!w_msrh_reset_n) begin
  end else begin
    if (u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.w_l1d_wr_if.valid &
        (u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.w_l1d_wr_if.paddr == 'h8000_1000)) begin
      $write("===============================\n");
      $write("SIMULATION FINISH : ");
      if (u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.w_l1d_wr_if.data[31: 0] == 32'h1) begin
        $write("PASS\n");
      end else begin
        $write("FAIL(%x)\n", u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.w_l1d_wr_if.data[31: 0]);
      end
      $write("===============================\n");
      $finish;
    end
  end // else: !if(!w_msrh_reset_n)
end // always_ff @ (negedge w_clk, negedge w_msrh_reset_n)

final begin
  $fclose(log_fp);
  $fclose(pipe_fp);
end
