// ------------------------------------------------------------------------
// NAME : JSON style performance dumper
// TYPE : module
// ------------------------------------------------------------------------
// Performance Information Dump gathered from each module
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

`ifdef MONITOR

int perf_fp;

initial begin
  perf_fp = $fopen("perf.json", "w");
  $fwrite(perf_fp, "{\n");
end

final begin
  $fwrite(perf_fp, "}\n");
  $fclose(perf_fp);
end

logic [63: 0] r_cycle_count;

always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
  if (!w_scariv_reset_n) begin
    r_cycle_count <= 'h0;
  end else begin
    r_cycle_count <= r_cycle_count + 'h1;

    if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      $fwrite(perf_fp, "\"%t\" : {\n", $time);

      // Instruction Buffer
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_frontend.u_scariv_inst_buffer.dump_perf(perf_fp);
      // Commit Rate
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.dump_perf(perf_fp);
      // ICache
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_frontend.u_scariv_icache.dump_perf(perf_fp);
      // DCache
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.u_scariv_dcache.dump_perf(perf_fp);
      // LDQ
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.u_ldq.dump_perf(perf_fp);
      // STQ
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.u_stq.dump_perf(perf_fp);

    end
  end // else: !if(!w_scariv_reset_n)
end // always_ff @ (negedge w_clk, negedge w_scariv_reset_n)


generate for (genvar a_idx = 0; a_idx < scariv_conf_pkg::ALU_INST_NUM; a_idx++) begin
  always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
    if (!w_scariv_reset_n) begin
    end else begin
      if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
        // ALU
        u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[a_idx].u_alu.u_scariv_issue_unit.dump_perf("alu", perf_fp);
      end
    end
  end
end
endgenerate


always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
  if (!w_scariv_reset_n) begin
  end else begin
    if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      $fwrite(perf_fp, "\}\n");
    end
  end
end

`endif // MONITOR
