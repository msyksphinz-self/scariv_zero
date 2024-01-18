`ifdef MONITOR

localparam ooo_count_valid = 1'b1;

generate if (ooo_count_valid) begin : ooo_monitor_count

  localparam ALU_ISSUE_BASE = 0;
  localparam LSU_ISSUE_BASE = scariv_conf_pkg::ALU_INST_NUM;
  localparam BRU_ISSUE_BASE = LSU_ISSUE_BASE + scariv_conf_pkg::LSU_INST_NUM;
  localparam CSU_ISSUE_BASE = BRU_ISSUE_BASE + 1;
  localparam FPU_ISSUE_BASE = CSU_ISSUE_BASE + 1;

  localparam ISSUE_UNIT_NUM = FPU_ISSUE_BASE + scariv_conf_pkg::FPU_INST_NUM;

  int unit_oldest_entries[ISSUE_UNIT_NUM-1: 0];


  // ---------------------------
  // ALU Issue Unit Information
  // ---------------------------
  for (genvar alu_idx = 0; alu_idx < scariv_conf_pkg::ALU_INST_NUM; alu_idx++) begin : alu_issue_loop
    /* verilator lint_off UNOPTFLAT */
    scariv_pkg::cmt_id_t w_alu_oldest_cmt_id[scariv_conf_pkg::RV_ALU_ENTRY_SIZE];
    scariv_pkg::grp_id_t w_alu_oldest_grp_id[scariv_conf_pkg::RV_ALU_ENTRY_SIZE];

    for (genvar entry_idx = 0; entry_idx < scariv_conf_pkg::RV_ALU_ENTRY_SIZE; entry_idx++) begin
    logic w_id0_is_older_than_id1;
      assign w_id0_is_older_than_id1 = scariv_pkg::id0_is_older_than_id1 (entry_idx == 'h0 ? 'h0 : w_alu_oldest_cmt_id[entry_idx-1],
                                                                          entry_idx == 'h0 ? 'h0 : w_alu_oldest_grp_id[entry_idx-1],
                                                                          u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[alu_idx].u_alu.u_scariv_issue_unit.w_entry[entry_idx].cmt_id,
                                                                          u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[alu_idx].u_alu.u_scariv_issue_unit.w_entry[entry_idx].grp_id);

      assign {w_alu_oldest_cmt_id[entry_idx],
              w_alu_oldest_grp_id[entry_idx]} = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[alu_idx].u_alu.u_scariv_issue_unit.w_entry[entry_idx].valid &
                                                ~u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[alu_idx].u_alu.u_scariv_issue_unit.entry_loop[entry_idx].u_issue_entry.r_issued &
                                                w_id0_is_older_than_id1 ?
                                                {u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[alu_idx].u_alu.u_scariv_issue_unit.w_entry[entry_idx].cmt_id,
                                                 u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[alu_idx].u_alu.u_scariv_issue_unit.w_entry[entry_idx].grp_id} :
                                                entry_idx == 'h0 ? 'h0 :
                                                {w_alu_oldest_cmt_id[entry_idx-1], w_alu_oldest_grp_id[entry_idx-1]};

    end // for (genvar entry_idx = 0; entry_idx < u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[alu_idx].u_alu.u_scariv_issue_unit.ENTRY_SIZE; entry_idx++)

    always_comb begin
      unit_oldest_entries[ALU_ISSUE_BASE + alu_idx] = {w_alu_oldest_cmt_id[scariv_conf_pkg::RV_ALU_ENTRY_SIZE-1],
                                                 w_alu_oldest_grp_id[scariv_conf_pkg::RV_ALU_ENTRY_SIZE-1]};
    end
  end // block: alu_issue_loop

  // ---------------------------
  // LSU Issue Unit Information
  // ---------------------------
  for (genvar lsu_idx = 0; lsu_idx < scariv_conf_pkg::LSU_INST_NUM; lsu_idx++) begin : lsu_issue_loop
    /* verilator lint_off UNOPTFLAT */
    scariv_pkg::cmt_id_t w_lsu_oldest_cmt_id[scariv_conf_pkg::RV_LSU_ENTRY_SIZE / scariv_conf_pkg::LSU_INST_NUM];
    scariv_pkg::grp_id_t w_lsu_oldest_grp_id[scariv_conf_pkg::RV_LSU_ENTRY_SIZE / scariv_conf_pkg::LSU_INST_NUM];

    for (genvar entry_idx = 0; entry_idx < scariv_conf_pkg::RV_LSU_ENTRY_SIZE / scariv_conf_pkg::LSU_INST_NUM; entry_idx++) begin
    logic w_id0_is_older_than_id1;
      assign w_id0_is_older_than_id1 = scariv_pkg::id0_is_older_than_id1 (entry_idx == 'h0 ? 'h0 : w_lsu_oldest_cmt_id[entry_idx-1],
                                                                          entry_idx == 'h0 ? 'h0 : w_lsu_oldest_grp_id[entry_idx-1],
                                                                          u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[lsu_idx].u_scariv_lsu.u_issue_unit.w_entry[entry_idx].cmt_id,
                                                                          u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[lsu_idx].u_scariv_lsu.u_issue_unit.w_entry[entry_idx].grp_id);

      assign {w_lsu_oldest_cmt_id[entry_idx],
              w_lsu_oldest_grp_id[entry_idx]} = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[lsu_idx].u_scariv_lsu.u_issue_unit.w_entry[entry_idx].valid &
                                                ~u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[lsu_idx].u_scariv_lsu.u_issue_unit.entry_loop[entry_idx].u_entry.r_issued &
                                                w_id0_is_older_than_id1 ?
                                                {u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[lsu_idx].u_scariv_lsu.u_issue_unit.w_entry[entry_idx].cmt_id,
                                                 u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[lsu_idx].u_scariv_lsu.u_issue_unit.w_entry[entry_idx].grp_id} :
                                                entry_idx == 'h0 ? 'h0 :
                                                {w_lsu_oldest_cmt_id[entry_idx-1], w_lsu_oldest_grp_id[entry_idx-1]};

    end // for (genvar entry_idx = 0; entry_idx < u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[lsu_idx].u_scariv_lsu.u_issue_unit.ENTRY_SIZE; entry_idx++)

    always_comb begin
      unit_oldest_entries[LSU_ISSUE_BASE + lsu_idx] = {w_lsu_oldest_cmt_id[scariv_conf_pkg::RV_LSU_ENTRY_SIZE / scariv_conf_pkg::LSU_INST_NUM-1],
                                                 w_lsu_oldest_grp_id[scariv_conf_pkg::RV_LSU_ENTRY_SIZE / scariv_conf_pkg::LSU_INST_NUM-1]};
    end
  end // block: lsu_issue_loop


  // ---------------------------
  // BRU Issue Unit Information
  // ---------------------------
  /* verilator lint_off UNOPTFLAT */
  scariv_pkg::cmt_id_t w_bru_oldest_cmt_id[scariv_conf_pkg::RV_BRU_ENTRY_SIZE];
  scariv_pkg::grp_id_t w_bru_oldest_grp_id[scariv_conf_pkg::RV_BRU_ENTRY_SIZE];
  for (genvar entry_idx = 0; entry_idx < scariv_conf_pkg::RV_BRU_ENTRY_SIZE; entry_idx++) begin: bru_issue_loop
  logic w_id0_is_older_than_id1;
    assign w_id0_is_older_than_id1 = scariv_pkg::id0_is_older_than_id1 (entry_idx == 'h0 ? 'h0 : w_bru_oldest_cmt_id[entry_idx-1],
                                                                        entry_idx == 'h0 ? 'h0 : w_bru_oldest_grp_id[entry_idx-1],
                                                                        u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_bru.u_issue_unit.w_entry[entry_idx].cmt_id,
                                                                        u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_bru.u_issue_unit.w_entry[entry_idx].grp_id);

    assign {w_bru_oldest_cmt_id[entry_idx],
            w_bru_oldest_grp_id[entry_idx]} = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_bru.u_issue_unit.w_entry[entry_idx].valid &
                                              ~u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_bru.u_issue_unit.entry_loop[entry_idx].u_issue_entry.r_issued &
                                              w_id0_is_older_than_id1 ?
                                              {u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_bru.u_issue_unit.w_entry[entry_idx].cmt_id,
                                               u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_bru.u_issue_unit.w_entry[entry_idx].grp_id} :
                                              entry_idx == 'h0 ? 'h0 :
                                              {w_bru_oldest_cmt_id[entry_idx-1], w_bru_oldest_grp_id[entry_idx-1]};

  end // block: bru_issue_loop

  always_comb begin
    unit_oldest_entries[BRU_ISSUE_BASE] = {w_bru_oldest_cmt_id[scariv_conf_pkg::RV_BRU_ENTRY_SIZE-1],
                                     w_bru_oldest_grp_id[scariv_conf_pkg::RV_BRU_ENTRY_SIZE-1]};
  end

  // ---------------------------
  // CSU Issue Unit Information
  // ---------------------------
  /* verilator lint_off UNOPTFLAT */
  scariv_pkg::cmt_id_t w_csu_oldest_cmt_id[scariv_conf_pkg::RV_CSU_ENTRY_SIZE];
  scariv_pkg::grp_id_t w_csu_oldest_grp_id[scariv_conf_pkg::RV_CSU_ENTRY_SIZE];
  for (genvar entry_idx = 0; entry_idx < scariv_conf_pkg::RV_CSU_ENTRY_SIZE; entry_idx++) begin: csu_issue_loop
  logic w_id0_is_older_than_id1;
    assign w_id0_is_older_than_id1 = scariv_pkg::id0_is_older_than_id1 (entry_idx == 'h0 ? 'h0 : w_csu_oldest_cmt_id[entry_idx-1],
                                                                        entry_idx == 'h0 ? 'h0 : w_csu_oldest_grp_id[entry_idx-1],
                                                                        u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_csu.u_scariv_issue_unit.w_entry[entry_idx].cmt_id,
                                                                        u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_csu.u_scariv_issue_unit.w_entry[entry_idx].grp_id);

    assign {w_csu_oldest_cmt_id[entry_idx],
            w_csu_oldest_grp_id[entry_idx]} = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_csu.u_scariv_issue_unit.w_entry[entry_idx].valid &
                                              ~u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_csu.u_scariv_issue_unit.entry_loop[entry_idx].u_issue_entry.r_issued &
                                              w_id0_is_older_than_id1 ?
                                              {u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_csu.u_scariv_issue_unit.w_entry[entry_idx].cmt_id,
                                               u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_csu.u_scariv_issue_unit.w_entry[entry_idx].grp_id} :
                                              entry_idx == 'h0 ? 'h0 :
                                              {w_csu_oldest_cmt_id[entry_idx-1], w_csu_oldest_grp_id[entry_idx-1]};

  end // block: csu_issue_loop

  always_comb begin
    unit_oldest_entries[CSU_ISSUE_BASE] = {w_csu_oldest_cmt_id[scariv_conf_pkg::RV_CSU_ENTRY_SIZE-1],
                                     w_csu_oldest_grp_id[scariv_conf_pkg::RV_CSU_ENTRY_SIZE-1]};
  end

  // ---------------------------
  // FPU Issue Unit Information
  // ---------------------------
  for (genvar fpu_idx = 0; fpu_idx < scariv_conf_pkg::FPU_INST_NUM; fpu_idx++) begin : fpu_issue_loop
    /* verilator lint_off UNOPTFLAT */
    scariv_pkg::cmt_id_t w_fpu_oldest_cmt_id[scariv_conf_pkg::RV_FPU_ENTRY_SIZE];
    scariv_pkg::grp_id_t w_fpu_oldest_grp_id[scariv_conf_pkg::RV_FPU_ENTRY_SIZE];

    for (genvar entry_idx = 0; entry_idx < scariv_conf_pkg::RV_FPU_ENTRY_SIZE; entry_idx++) begin
    logic w_id0_is_older_than_id1;
      assign w_id0_is_older_than_id1 = scariv_pkg::id0_is_older_than_id1 (entry_idx == 'h0 ? 'h0 : w_fpu_oldest_cmt_id[entry_idx-1],
                                                                          entry_idx == 'h0 ? 'h0 : w_fpu_oldest_grp_id[entry_idx-1],
                                                                          u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.fpu_loop[fpu_idx].u_fpu.u_scariv_issue_unit.w_entry[entry_idx].cmt_id,
                                                                          u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.fpu_loop[fpu_idx].u_fpu.u_scariv_issue_unit.w_entry[entry_idx].grp_id);

      assign {w_fpu_oldest_cmt_id[entry_idx],
              w_fpu_oldest_grp_id[entry_idx]} = u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.fpu_loop[fpu_idx].u_fpu.u_scariv_issue_unit.w_entry[entry_idx].valid &
                                                ~u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.fpu_loop[fpu_idx].u_fpu.u_scariv_issue_unit.entry_loop[entry_idx].u_issue_entry.r_issued &
                                                w_id0_is_older_than_id1 ?
                                                {u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.fpu_loop[fpu_idx].u_fpu.u_scariv_issue_unit.w_entry[entry_idx].cmt_id,
                                                 u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.fpu_loop[fpu_idx].u_fpu.u_scariv_issue_unit.w_entry[entry_idx].grp_id} :
                                                entry_idx == 'h0 ? 'h0 :
                                                {w_fpu_oldest_cmt_id[entry_idx-1], w_fpu_oldest_grp_id[entry_idx-1]};

    end // for (genvar entry_idx = 0; entry_idx < u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.fpu_loop[fpu_idx].u_fpu.u_scariv_issue_unit.ENTRY_SIZE; entry_idx++)

    always_comb begin
      unit_oldest_entries[FPU_ISSUE_BASE + fpu_idx] = {w_fpu_oldest_cmt_id[scariv_conf_pkg::RV_FPU_ENTRY_SIZE-1],
                                                 w_fpu_oldest_grp_id[scariv_conf_pkg::RV_FPU_ENTRY_SIZE-1]};
    end
  end // block: fpu_issue_loop

  scariv_pkg::cmt_id_t w_scheduler_oldest_cmt_id;
  scariv_pkg::grp_id_t w_scheduler_oldest_grp_id;
  int                  w_scheduler_oldest_id;

  always_comb begin
    w_scheduler_oldest_cmt_id = '0;
    w_scheduler_oldest_grp_id = '0;
    w_scheduler_oldest_id = 'h0;
    for (int i = 0; i < scariv_conf_pkg::ALU_INST_NUM + scariv_conf_pkg::LSU_INST_NUM + 1 + 1 + scariv_conf_pkg::FPU_INST_NUM; i++) begin
      if ((unit_oldest_entries[i] != 'h0) &
          (({w_scheduler_oldest_cmt_id, w_scheduler_oldest_grp_id} == 'h0) |
           ({w_scheduler_oldest_cmt_id, w_scheduler_oldest_grp_id}) > unit_oldest_entries[i])) begin
        {w_scheduler_oldest_cmt_id, w_scheduler_oldest_grp_id} = unit_oldest_entries[i];
        w_scheduler_oldest_id = unit_oldest_entries[i];
      end
    end
  end

  // ----------------------
  // Counting Up OoO issue
  // ----------------------
  logic [ 9: 0] r_issue_num[ISSUE_UNIT_NUM-1: 0];
  logic [ 9: 0] r_ooo_issue_num[ISSUE_UNIT_NUM-1: 0];

  logic [ 9: 0]   r_count;
  logic           w_count_reset;
  always_ff @ (posedge w_clk, negedge w_scariv_reset_n) begin
    if (!w_scariv_reset_n) begin
      r_count <= 'h0;
    end else begin
      if (r_count == 1000-1) begin
        r_count <= 'h0;
      end else begin
        r_count <= r_count + 'h1;
      end
    end
  end
  assign w_count_reset = r_count == 1000-1;

  for (genvar alu_idx = 0; alu_idx < scariv_conf_pkg::ALU_INST_NUM; alu_idx++) begin : alu_issue_count_loop
    always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
      if (!w_scariv_reset_n | w_count_reset) begin
        r_issue_num    [ALU_ISSUE_BASE + alu_idx] <= 'h0;
        r_ooo_issue_num[ALU_ISSUE_BASE + alu_idx] <= 'h0;
      end else begin
        if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[alu_idx].u_alu.w_rv0_issue.valid) begin
          r_issue_num    [ALU_ISSUE_BASE + alu_idx] <= r_issue_num[ALU_ISSUE_BASE + alu_idx] + 'h1;
          if (scariv_pkg::id0_is_older_than_id1 (w_scheduler_oldest_cmt_id, w_scheduler_oldest_grp_id,
                                                 u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[alu_idx].u_alu.w_rv0_issue.cmt_id,
                                                 u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.alu_loop[alu_idx].u_alu.w_rv0_issue.grp_id)) begin
            r_ooo_issue_num[ALU_ISSUE_BASE + alu_idx] <= r_ooo_issue_num[ALU_ISSUE_BASE + alu_idx] + 'h1;
          end
        end
      end // else: !if(!w_scariv_reset_n | w_count_reset)
    end // always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
  end

  for (genvar lsu_idx = 0; lsu_idx < scariv_conf_pkg::LSU_INST_NUM; lsu_idx++) begin : lsu_issue_count_loop
    always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
      if (!w_scariv_reset_n | w_count_reset) begin
        r_issue_num    [LSU_ISSUE_BASE + lsu_idx] <= 'h0;
        r_ooo_issue_num[LSU_ISSUE_BASE + lsu_idx] <= 'h0;
      end else begin
        if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[lsu_idx].u_scariv_lsu.w_issue_from_iss.valid) begin
          r_issue_num    [LSU_ISSUE_BASE + lsu_idx] <= r_issue_num[LSU_ISSUE_BASE + lsu_idx] + 'h1;

          if (scariv_pkg::id0_is_older_than_id1 (w_scheduler_oldest_cmt_id, w_scheduler_oldest_grp_id,
                                                 u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[lsu_idx].u_scariv_lsu.w_issue_from_iss.cmt_id,
                                                 u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_lsu_top.lsu_loop[lsu_idx].u_scariv_lsu.w_issue_from_iss.grp_id)) begin
            r_ooo_issue_num[LSU_ISSUE_BASE + lsu_idx] <= r_ooo_issue_num[LSU_ISSUE_BASE + lsu_idx] + 'h1;
          end
        end
      end // else: !if(!w_scariv_reset_n | w_count_reset)
    end // always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
  end

  // BRU
  always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
    if (!w_scariv_reset_n | w_count_reset) begin
      r_issue_num    [BRU_ISSUE_BASE] <= 'h0;
      r_ooo_issue_num[BRU_ISSUE_BASE] <= 'h0;
    end else begin
      if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_bru.w_rv0_issue.valid) begin
        r_issue_num    [BRU_ISSUE_BASE] <= r_issue_num[BRU_ISSUE_BASE] + 'h1;
        if (scariv_pkg::id0_is_older_than_id1 (w_scheduler_oldest_cmt_id, w_scheduler_oldest_grp_id,
                                               u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_bru.w_rv0_issue.cmt_id,
                                               u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_bru.w_rv0_issue.grp_id)) begin
          r_ooo_issue_num[BRU_ISSUE_BASE] <= r_ooo_issue_num[BRU_ISSUE_BASE] + 'h1;
        end
      end
    end // else: !if(!w_scariv_reset_n | w_count_reset)
  end // always_ff @ (negedge w_clk, negedge w_scariv_reset_n)

  // CSU
  always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
    if (!w_scariv_reset_n | w_count_reset) begin
      r_issue_num    [CSU_ISSUE_BASE] <= 'h0;
      r_ooo_issue_num[CSU_ISSUE_BASE] <= 'h0;
    end else begin
      if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_csu.w_rv0_issue.valid) begin
        r_issue_num    [CSU_ISSUE_BASE] <= r_issue_num[CSU_ISSUE_BASE] + 'h1;
        if (scariv_pkg::id0_is_older_than_id1 (w_scheduler_oldest_cmt_id, w_scheduler_oldest_grp_id,
                                               u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_csu.w_rv0_issue.cmt_id,
                                               u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.u_csu.w_rv0_issue.grp_id)) begin
          r_ooo_issue_num[CSU_ISSUE_BASE] <= r_ooo_issue_num[CSU_ISSUE_BASE] + 'h1;
        end
      end
    end // else: !if(!w_scariv_reset_n | w_count_reset)
  end // always_ff @ (negedge w_clk, negedge w_scariv_reset_n)


  for (genvar fpu_idx = 0; fpu_idx < scariv_conf_pkg::FPU_INST_NUM; fpu_idx++) begin : fpu_issue_count_loop
    always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
      if (!w_scariv_reset_n | w_count_reset) begin
        r_issue_num    [FPU_ISSUE_BASE + fpu_idx] <= 'h0;
        r_ooo_issue_num[FPU_ISSUE_BASE + fpu_idx] <= 'h0;
      end else begin
        if (u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.fpu_loop[fpu_idx].u_fpu.w_ex0_issue.valid) begin
          r_issue_num    [FPU_ISSUE_BASE + fpu_idx] <= r_issue_num[FPU_ISSUE_BASE + fpu_idx] + 'h1;
          if (scariv_pkg::id0_is_older_than_id1 (w_scheduler_oldest_cmt_id, w_scheduler_oldest_grp_id,
                                                 u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.fpu_loop[fpu_idx].u_fpu.w_ex0_issue.cmt_id,
                                                 u_scariv_subsystem_wrapper.u_scariv_subsystem.u_tile.fpu.fpu_loop[fpu_idx].u_fpu.w_ex0_issue.grp_id)) begin
            r_ooo_issue_num[FPU_ISSUE_BASE + fpu_idx] <= r_ooo_issue_num[FPU_ISSUE_BASE + fpu_idx] + 'h1;
          end
        end
      end // else: !if(!w_scariv_reset_n | w_count_reset)
    end // always_ff @ (negedge w_clk, negedge w_scariv_reset_n)
  end // block: fpu_issue_count_loop


  integer ooo_issue_fp;

  logic [15: 0] r_total_issue_num;
  logic [15: 0] r_total_ooo_issue_num;
  logic [31: 0] r_sim_total_issue_num;
  logic [31: 0] r_sim_total_ooo_issue_num;

  initial begin
    ooo_issue_fp = $fopen("ooo_issue.txt", "w");
  end
  final begin
    $fwrite(ooo_issue_fp, "======================================\n");
    $fwrite(ooo_issue_fp, "Final rate %7d / %7d = %0.3f\n", r_sim_total_ooo_issue_num, r_sim_total_issue_num, real'(r_sim_total_ooo_issue_num) / real'(r_sim_total_issue_num));
    $fwrite(ooo_issue_fp, "======================================\n");
    $fclose(ooo_issue_fp);
  end


  always_ff @ (negedge w_clk, negedge w_scariv_reset_n) begin
    if (!w_scariv_reset_n) begin
      r_sim_total_issue_num     = 'h0;
      r_sim_total_ooo_issue_num = 'h0;
    end else if (w_count_reset) begin
      r_sim_total_issue_num = r_sim_total_issue_num + r_total_issue_num;
      r_sim_total_ooo_issue_num = r_sim_total_ooo_issue_num + r_total_ooo_issue_num;

      r_total_issue_num = 'h0;
      r_total_ooo_issue_num = 'h0;
      for (int alu_idx = 0; alu_idx < scariv_conf_pkg::ALU_INST_NUM; alu_idx++) begin : alu_issue_fp_write
        $fwrite(ooo_issue_fp, "alu[%1d] %3d / %3d, ", alu_idx, r_ooo_issue_num[ALU_ISSUE_BASE + alu_idx], r_issue_num[ALU_ISSUE_BASE + alu_idx]);
        r_total_issue_num = r_total_issue_num + r_issue_num    [ALU_ISSUE_BASE + alu_idx];
        r_total_ooo_issue_num   = r_total_ooo_issue_num   + r_ooo_issue_num[ALU_ISSUE_BASE + alu_idx];
      end
      for (int lsu_idx = 0; lsu_idx < scariv_conf_pkg::LSU_INST_NUM; lsu_idx++) begin : lsu_issue_fp_write
        $fwrite(ooo_issue_fp, "lsu[%1d] %3d / %3d, ", lsu_idx, r_ooo_issue_num[LSU_ISSUE_BASE + lsu_idx], r_issue_num[LSU_ISSUE_BASE + lsu_idx]);
        r_total_issue_num = r_total_issue_num + r_issue_num    [LSU_ISSUE_BASE + lsu_idx];
        r_total_ooo_issue_num   = r_total_ooo_issue_num   + r_ooo_issue_num[LSU_ISSUE_BASE + lsu_idx];
      end
      $fwrite(ooo_issue_fp, "bru %3d / %3d, ", r_ooo_issue_num[BRU_ISSUE_BASE], r_issue_num[BRU_ISSUE_BASE]);
      r_total_issue_num = r_total_issue_num + r_issue_num    [BRU_ISSUE_BASE];
      r_total_ooo_issue_num   = r_total_ooo_issue_num   + r_ooo_issue_num[BRU_ISSUE_BASE];
      $fwrite(ooo_issue_fp, "csu %3d / %3d, ", r_ooo_issue_num[CSU_ISSUE_BASE], r_issue_num[CSU_ISSUE_BASE]);
      r_total_issue_num = r_total_issue_num + r_issue_num    [CSU_ISSUE_BASE];
      r_total_ooo_issue_num   = r_total_ooo_issue_num   + r_ooo_issue_num[CSU_ISSUE_BASE];
      for (int fpu_idx = 0; fpu_idx < scariv_conf_pkg::FPU_INST_NUM; fpu_idx++) begin : fpu_issue_fp_write
        $fwrite(ooo_issue_fp, "fpu[%1d] %3d / %3d, ", fpu_idx, r_ooo_issue_num[FPU_ISSUE_BASE + fpu_idx], r_issue_num[FPU_ISSUE_BASE + fpu_idx]);
        r_total_issue_num = r_total_issue_num + r_issue_num    [FPU_ISSUE_BASE + fpu_idx];
        r_total_ooo_issue_num   = r_total_ooo_issue_num   + r_ooo_issue_num[FPU_ISSUE_BASE + fpu_idx];
      end
      $fwrite(ooo_issue_fp, "%5d / %5d = %0.3f", r_total_ooo_issue_num, r_total_issue_num, real'(r_total_ooo_issue_num) / real'(r_total_issue_num));
      $fwrite(ooo_issue_fp, "\n");
    end // if (w_count_reset)
  end // always_ff @ (negedge w_clk, negedge w_scariv_reset_n)

end endgenerate // block: ooo_monitor_count


`endif //  `ifdef MONITOR
