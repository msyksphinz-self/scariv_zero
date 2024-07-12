`ifdef MONITOR

localparam dump_json_enable = 1'b0;

generate if (dump_json_enable) begin : dump_json

int json_fp;

  initial begin
    json_fp = $fopen("dump.json", "w");
    $fwrite(json_fp, "{\n");
  end

  final begin
    $fwrite(json_fp, "}\n");
    $fclose(json_fp);
  end

  always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
    if (w_scariv_reset_n) begin
      // Initial and Time
      $fwrite(json_fp, "\"%t\" : {\n", $time);

      // ICache
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_frontend.u_scariv_icache.dump_json(json_fp);
      // Inst Buffer
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_frontend.u_front_decoder.dump_json(json_fp);
      // Rename --> Dispatch
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rename.dump_json("int", json_fp);

      // LSU LDQ
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.u_ldq.dump_json(json_fp);
      // LSU STQ
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.u_stq.dump_json(json_fp);

      // LSU LRQ
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.u_l1d_mshr.dump_json(json_fp);

      // BRU Scheduler
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_bru.u_issue_unit.dump_json("bru", json_fp, 0);

      // CSU Scheduler
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_csu.u_scariv_issue_unit.dump_json("csu", json_fp, 0);

      // ROB
      u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_rob.dump_json(json_fp);
    end // if (w_scariv_reset_n)
  end // always_ff @ (negedge w_clk, negedge w_scariv_reset_n)


  // ALU Scheduler
  if (scariv_conf_pkg::ALU_INST_NUM > 0)
    always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
      if (w_scariv_reset_n) begin
        u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[0].u_alu.u_scariv_issue_unit.dump_json("alu0", json_fp, 0);
      end

  if (scariv_conf_pkg::ALU_INST_NUM > 1)
    always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
      if (w_scariv_reset_n) begin
        u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[1].u_alu.u_scariv_issue_unit.dump_json("alu1", json_fp, 1);
      end

  if (scariv_conf_pkg::ALU_INST_NUM > 2)
    always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
      if (w_scariv_reset_n) begin
        u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[2].u_alu.u_scariv_issue_unit.dump_json("alu2", json_fp, 2);
      end

  if (scariv_conf_pkg::ALU_INST_NUM > 3)
    always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
      if (w_scariv_reset_n) begin
        u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[3].u_alu.u_scariv_issue_unit.dump_json("alu3", json_fp, 3);
      end

  if (scariv_conf_pkg::ALU_INST_NUM > 4)
    always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
      if (w_scariv_reset_n) begin
        u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[4].u_alu.u_scariv_issue_unit.dump_json("alu4", json_fp, 4);
      end

  if (scariv_conf_pkg::ALU_INST_NUM > 5)
    always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
      if (w_scariv_reset_n) begin
        u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[5].u_alu.u_scariv_issue_unit.dump_json("alu5", json_fp, 5);
      end

  // // LSU Scheduler
  // generate if (scariv_conf_pkg::LSU_INST_NUM > 0)
  //   always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
  //     if (w_scariv_reset_n) begin
  //       u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[0].u_scariv_lsu.u_scariv_issue_unit.dump_json("lsu0", json_fp, 0);
  //     end
  // endgenerate
  // generate if (scariv_conf_pkg::LSU_INST_NUM > 1)
  //   always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
  //     if (w_scariv_reset_n) begin
  //       u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[1].u_scariv_lsu.u_scariv_issue_unit.dump_json("lsu1", json_fp, 1);
  //     end
  // endgenerate
  // generate if (scariv_conf_pkg::LSU_INST_NUM > 2)
  //   always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
  //     if (w_scariv_reset_n) begin
  //       u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[2].u_scariv_lsu.u_scariv_issue_unit.dump_json("lsu2", json_fp, 2);
  //     end
  // endgenerate
  // generate if (scariv_conf_pkg::LSU_INST_NUM > 3)
  //   always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
  //     if (w_scariv_reset_n) begin
  //       u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[3].u_scariv_lsu.u_scariv_issue_unit.dump_json("lsu3", json_fp, 3);
  //     end
  // endgenerate

  always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
    if (w_scariv_reset_n) begin
      $fwrite(json_fp, "%t}},\n", $time);
    end
  end

end // block: dump_json
endgenerate

`endif // MONITOR
