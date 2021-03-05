int json_fp;

initial begin
  json_fp = $fopen("dump.json", "w");
  $fwrite(json_fp, "{\n");
end

final begin
  $fwrite(json_fp, "}\n");
  $fclose(json_fp);
end

always_ff @ (negedge i_clk, negedge i_msrh_reset_n) begin
  // Initial and Time
  $fwrite(json_fp, "\"%t\" : {\n", $time);

  // ICache
  u_msrh_tile_wrapper.u_msrh_tile.u_frontend.u_msrh_icache.dump_json(json_fp);
  // Inst Buffer
  u_msrh_tile_wrapper.u_msrh_tile.u_frontend.u_msrh_inst_buffer.dump_json(json_fp);
  // Rename --> Dispatch
  u_msrh_tile_wrapper.u_msrh_tile.u_msrh_rename.dump_json(json_fp);

  // ALU Scheduler
  u_msrh_tile_wrapper.u_msrh_tile.alu_loop[0].u_msrh_alu.u_msrh_scheduler.dump_json(json_fp, 0);
  // u_msrh_tile_wrapper.u_msrh_tile.alu_loop[1].u_msrh_alu.u_msrh_scheduler.dump_json(json_fp, 1);

  // LSU Scheduler
  u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.lsu_loop[0].u_msrh_lsu.u_msrh_scheduler.dump_json(json_fp, 0);
  // u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.lsu_loop[1].u_msrh_lsu.u_msrh_scheduler.dump_json(json_fp, 1);

  // JSON End
  $fwrite(json_fp, "}\n");
end
