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

always_ff @ (negedge w_clk, negedge w_msrh_reset_n) begin
  if (!w_msrh_reset_n) begin
    r_cycle_count <= 'h0;
  end else begin
    r_cycle_count <= r_cycle_count + 'h1;

    if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      $fwrite(perf_fp, "\"%t\" : {\n", $time);

      // Commit Rate
      u_msrh_tile_wrapper.u_msrh_tile.u_rob.dump_perf(perf_fp);
      // ICache
      u_msrh_tile_wrapper.u_msrh_tile.u_frontend.u_msrh_icache.dump_perf(perf_fp);
      // DCache
      u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.u_msrh_dcache.dump_perf(perf_fp);
      // Branch
      u_msrh_tile_wrapper.u_msrh_tile.u_frontend.u_ftq.dump_branch_perf(perf_fp);

      $fwrite(perf_fp, "\}\n");
    end
  end // else: !if(!w_msrh_reset_n)
end // always_ff @ (negedge w_clk, negedge w_msrh_reset_n)

`endif // MONITOR
