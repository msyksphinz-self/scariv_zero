int json_fp;

initial begin
  json_fp = $fopen("dump.json", "w");
  $fwrite(json_fp, "{\n");
end

final begin
  $fwrite(json_fp, "}\n");
  $fclose(json_fp);
end

always_ff @ (negedge w_clk, negedge w_msrh_reset_n) begin
  // Initial and Time
  $fwrite(json_fp, "\"%t\" : {\n", $time);

  // ICache
  u_msrh_tile_wrapper.u_msrh_tile.u_frontend.u_msrh_icache.dump_json(json_fp);
  // Inst Buffer
  u_msrh_tile_wrapper.u_msrh_tile.u_frontend.u_msrh_inst_buffer.dump_json(json_fp);
  // Rename --> Dispatch
  u_msrh_tile_wrapper.u_msrh_tile.u_msrh_rename.dump_json(json_fp);

  // ALU Scheduler
  u_msrh_tile_wrapper.u_msrh_tile.alu_loop[0].u_msrh_alu.u_msrh_scheduler.dump_json("alu0", json_fp, 0);
  u_msrh_tile_wrapper.u_msrh_tile.alu_loop[1].u_msrh_alu.u_msrh_scheduler.dump_json("alu1", json_fp, 1);

  // LSU Scheduler
  u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.lsu_loop[0].u_msrh_lsu.u_msrh_scheduler.dump_json("lsu0", json_fp, 0);
  u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.lsu_loop[1].u_msrh_lsu.u_msrh_scheduler.dump_json("lsu1", json_fp, 1);

  // LSU LDQ
  u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.u_ldq.dump_json(json_fp);
  // LSU STQ
  u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.u_stq.dump_json(json_fp);

  // BRU Scheduler
  u_msrh_tile_wrapper.u_msrh_tile.u_msrh_bru.u_msrh_scheduler.dump_json("bru", json_fp, 0);

  // JSON End
  $fwrite(json_fp, "},\n");
end
