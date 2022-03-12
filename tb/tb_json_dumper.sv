`ifdef MONITOR

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
  if (w_msrh_reset_n) begin
    // Initial and Time
    $fwrite(json_fp, "\"%t\" : {\n", $time);

    // ICache
    u_msrh_tile_wrapper.u_msrh_tile.u_frontend.u_msrh_icache.dump_json(json_fp);
    // Inst Buffer
    u_msrh_tile_wrapper.u_msrh_tile.u_frontend.u_msrh_inst_buffer.dump_json(json_fp);
    // Rename --> Dispatch
    u_msrh_tile_wrapper.u_msrh_tile.u_msrh_int_rename.dump_json("int", json_fp);
    u_msrh_tile_wrapper.u_msrh_tile.u_msrh_fp_rename.dump_json("fp", json_fp);

    // LSU LDQ
    u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.u_ldq.dump_json(json_fp);
    // LSU STQ
    u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.u_stq.dump_json(json_fp);

    // LSU LRQ
    u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.u_miss_unit.dump_json(json_fp);

    // BRU Scheduler
    u_msrh_tile_wrapper.u_msrh_tile.u_msrh_bru.u_msrh_scheduler.dump_json("bru", json_fp, 0);

    // CSU Scheduler
    u_msrh_tile_wrapper.u_msrh_tile.u_msrh_csu.u_msrh_scheduler.dump_json("csu", json_fp, 0);

    // ROB
    u_msrh_tile_wrapper.u_msrh_tile.u_rob.dump_json(json_fp);
  end // if (!w_msrh_reset_n)
end // always_ff @ (negedge w_clk, negedge w_msrh_reset_n)

// ALU Scheduler
generate if (msrh_conf_pkg::ALU_INST_NUM > 0)
  always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
    if (w_msrh_reset_n) begin
      u_msrh_tile_wrapper.u_msrh_tile.alu_loop[0].u_msrh_alu.u_msrh_scheduler.dump_json("alu0", json_fp, 0);
    end
endgenerate
generate if (msrh_conf_pkg::ALU_INST_NUM > 1)
  always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
    if (w_msrh_reset_n) begin
      u_msrh_tile_wrapper.u_msrh_tile.alu_loop[1].u_msrh_alu.u_msrh_scheduler.dump_json("alu1", json_fp, 1);
    end
endgenerate
generate if (msrh_conf_pkg::ALU_INST_NUM > 2)
  always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
    if (w_msrh_reset_n) begin
      u_msrh_tile_wrapper.u_msrh_tile.alu_loop[2].u_msrh_alu.u_msrh_scheduler.dump_json("alu2", json_fp, 2);
    end
endgenerate
generate if (msrh_conf_pkg::ALU_INST_NUM > 3)
  always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
    if (w_msrh_reset_n) begin
      u_msrh_tile_wrapper.u_msrh_tile.alu_loop[3].u_msrh_alu.u_msrh_scheduler.dump_json("alu3", json_fp, 3);
    end
endgenerate
generate if (msrh_conf_pkg::ALU_INST_NUM > 4)
  always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
    if (w_msrh_reset_n) begin
      u_msrh_tile_wrapper.u_msrh_tile.alu_loop[4].u_msrh_alu.u_msrh_scheduler.dump_json("alu4", json_fp, 4);
    end
endgenerate
generate if (msrh_conf_pkg::ALU_INST_NUM > 5)
  always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
    if (w_msrh_reset_n) begin
      u_msrh_tile_wrapper.u_msrh_tile.alu_loop[5].u_msrh_alu.u_msrh_scheduler.dump_json("alu5", json_fp, 5);
    end
endgenerate

// // LSU Scheduler
// generate if (msrh_conf_pkg::LSU_INST_NUM > 0)
//   always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
//     if (w_msrh_reset_n) begin
//       u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.lsu_loop[0].u_msrh_lsu.u_msrh_scheduler.dump_json("lsu0", json_fp, 0);
//     end
// endgenerate
// generate if (msrh_conf_pkg::LSU_INST_NUM > 1)
//   always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
//     if (w_msrh_reset_n) begin
//       u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.lsu_loop[1].u_msrh_lsu.u_msrh_scheduler.dump_json("lsu1", json_fp, 1);
//     end
// endgenerate
// generate if (msrh_conf_pkg::LSU_INST_NUM > 2)
//   always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
//     if (w_msrh_reset_n) begin
//       u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.lsu_loop[2].u_msrh_lsu.u_msrh_scheduler.dump_json("lsu2", json_fp, 2);
//     end
// endgenerate
// generate if (msrh_conf_pkg::LSU_INST_NUM > 3)
//   always_ff @ (negedge w_clk, negedge w_msrh_reset_n)
//     if (w_msrh_reset_n) begin
//       u_msrh_tile_wrapper.u_msrh_tile.u_msrh_lsu_top.lsu_loop[3].u_msrh_lsu.u_msrh_scheduler.dump_json("lsu3", json_fp, 3);
//     end
// endgenerate

always_ff @ (negedge w_clk, negedge w_msrh_reset_n) begin
  if (w_msrh_reset_n) begin
    $fwrite(json_fp, "%t}},\n", $time);
  end
end

`endif // MONITOR
