module msrh_rename
  (
   input logic i_clk,
   input logic i_reset_n,

   disp_if.slave disp_from_frontend,
   input logic [msrh_pkg::CMT_BLK_W-1:0] i_new_cmt_id,
   disp_if.master disp_to_scheduler
   );

logic [$clog2(msrh_pkg::RNID_SIZE)-1: 0] w_rd_rnid[msrh_pkg::DISP_SIZE];

logic [msrh_pkg::DISP_SIZE * 2-1: 0]     w_archreg_valid;
logic [ 4: 0]                           w_archreg[msrh_pkg::DISP_SIZE * 2];
logic [msrh_pkg::RNID_W-1: 0]            w_rnid[msrh_pkg::DISP_SIZE * 2];

logic [ 4: 0]                            w_update_arch_id [msrh_pkg::DISP_SIZE];
logic [msrh_pkg::RNID_W-1: 0]            w_update_rnid    [msrh_pkg::DISP_SIZE];

msrh_pkg::disp_t [msrh_pkg::DISP_SIZE-1:0] w_disp_inst;

logic [msrh_pkg::RNID_W-1: 0]            rs1_rnid_fwd[msrh_pkg::DISP_SIZE];
logic [msrh_pkg::RNID_W-1: 0]            rs2_rnid_fwd[msrh_pkg::DISP_SIZE];

logic [msrh_pkg::DISP_SIZE * 2-1: 0]     w_active;

logic [msrh_pkg::DISP_SIZE-1: 0]         w_rd_valids;
logic [ 4: 0]                           w_rd_regidx[msrh_pkg::DISP_SIZE];
logic [msrh_pkg::DISP_SIZE-1: 0]         w_rd_data;

assign disp_from_frontend.ready = 1'b1;

generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : free_loop
  msrh_freelist
                             #(
                               .SIZE (msrh_pkg::FLIST_SIZE),
                               .WIDTH ($clog2(msrh_pkg::RNID_SIZE)),
                               .INIT (msrh_pkg::FLIST_SIZE * d_idx + 32)
                               )
  u_freelist
                             (
                              .i_clk     (i_clk ),
                              .i_reset_n (i_reset_n),

                              .i_push(disp_from_frontend.inst[d_idx].rd_valid),
                              .i_push_id(),

                              .i_pop(disp_from_frontend.inst[d_idx].valid & disp_from_frontend.inst[d_idx].rd_valid),
                              .o_pop_id(w_rd_rnid[d_idx])
                              );
end
endgenerate

generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : src_rd_loop
  assign w_archreg_valid [d_idx*2 + 0] = disp_from_frontend.inst[d_idx].rs1_valid;
  assign w_archreg_valid [d_idx*2 + 1] = disp_from_frontend.inst[d_idx].rs2_valid;

  assign w_archreg [d_idx*2 + 0] = disp_from_frontend.inst[d_idx].rs1_regidx;
  assign w_archreg [d_idx*2 + 1] = disp_from_frontend.inst[d_idx].rs2_regidx;

  assign w_update_arch_id[d_idx] = w_rd_regidx[d_idx];
  assign w_update_rnid   [d_idx] = w_rd_rnid[d_idx];

end
endgenerate

msrh_rename_map u_msrh_rename_map
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_arch_valid (w_archreg_valid),
   .i_arch_id    (w_archreg),
   .o_rnid       (w_rnid),

   .i_update         (w_rd_valids),
   .i_update_arch_id (w_update_arch_id),
   .i_update_rnid    (w_update_rnid   )
   );


generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : rd_loop
  assign w_rd_valids[d_idx] = disp_from_frontend.inst[d_idx].rd_valid;
  assign w_rd_regidx[d_idx] = disp_from_frontend.inst[d_idx].rd_regidx;
  assign w_rd_data  [d_idx] = !disp_from_frontend.inst[d_idx].rd_valid;
end
endgenerate

msrh_inflight_list u_inflight_map
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_addr   (w_archreg),
   .o_valids (w_active),

   .i_update_fetch_vld (w_rd_valids),
   .i_update_fetch_addr(w_rd_regidx),
   .i_update_fetch_data(w_rd_data  ),

   .i_update_cmt_vld (),
   .i_update_cmt_addr(),
   .i_update_cmt_data()

);

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    disp_to_scheduler.valid <= 'h0;
    disp_to_scheduler.pc_addr <= 'h0;
    // disp_to_scheduler.cmt_id <= 'h0;
    disp_to_scheduler.inst <= 'h0;
  end else begin
    disp_to_scheduler.valid  <= disp_from_frontend.valid;
    disp_to_scheduler.pc_addr <= disp_from_frontend.pc_addr;
    // disp_to_scheduler.cmt_id <= i_new_cmt_id;
    disp_to_scheduler.inst   <= w_disp_inst;
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign disp_to_scheduler.cmt_id = i_new_cmt_id;

generate for (genvar d_idx = 0; d_idx < msrh_pkg::DISP_SIZE; d_idx++) begin : src_rn_loop
  /* verilator lint_off UNOPTFLAT */
  logic [msrh_pkg::RNID_W-1: 0] rs1_rnid_tmp[msrh_pkg::DISP_SIZE];
  logic [msrh_pkg::DISP_SIZE-1: 0] rs1_rnid_tmp_valid;

  logic [msrh_pkg::RNID_W-1: 0] rs2_rnid_tmp[msrh_pkg::DISP_SIZE];
  logic [msrh_pkg::DISP_SIZE-1: 0] rs2_rnid_tmp_valid;

  always_comb begin

    /* initial index of loop */
    if (disp_from_frontend.inst[0].rd_valid &&
        disp_from_frontend.inst[0].rd_type   == disp_from_frontend.inst[d_idx].rs1_type &&
        disp_from_frontend.inst[0].rd_regidx == disp_from_frontend.inst[d_idx].rs1_regidx) begin
      rs1_rnid_tmp_valid[0] = 1'b1;
      rs1_rnid_tmp      [0] = w_rd_rnid[0];
    end else begin
      rs1_rnid_tmp_valid[0] = 1'b0;
      rs1_rnid_tmp      [0] = w_rnid[d_idx * 2 + 0];
    end

    if (disp_from_frontend.inst[0].rd_valid &&
        disp_from_frontend.inst[0].rd_type   == disp_from_frontend.inst[d_idx].rs2_type &&
        disp_from_frontend.inst[0].rd_regidx == disp_from_frontend.inst[d_idx].rs2_regidx) begin
      rs2_rnid_tmp_valid[0] = 1'b1;
      rs2_rnid_tmp      [0] = w_rd_rnid[0];
    end else begin
      rs2_rnid_tmp_valid[0] = 1'b0;
      rs2_rnid_tmp      [0] = w_rnid[d_idx * 2 + 1];
    end // else: !if(disp_from_frontend.inst[p_idx].rd_valid &&...

    /* verilator lint_off UNSIGNED */
    for (int p_idx = 1; p_idx < d_idx; p_idx++) begin: prev_rd_loop
      if (disp_from_frontend.inst[p_idx].rd_valid &&
          disp_from_frontend.inst[p_idx].rd_type   == disp_from_frontend.inst[d_idx].rs1_type &&
          disp_from_frontend.inst[p_idx].rd_regidx == disp_from_frontend.inst[d_idx].rs1_regidx) begin
        rs1_rnid_tmp_valid[p_idx] = 1'b1;
        rs1_rnid_tmp[p_idx] = w_rd_rnid[p_idx];
      end else begin
        rs1_rnid_tmp_valid[p_idx] = rs1_rnid_tmp_valid[p_idx-1];
        rs1_rnid_tmp      [p_idx] = rs1_rnid_tmp      [p_idx-1];
      end // else: !if(disp_from_frontend.inst[p_idx].rd_valid &&...

      if (disp_from_frontend.inst[p_idx].rd_valid &&
          disp_from_frontend.inst[p_idx].rd_type   == disp_from_frontend.inst[d_idx].rs2_type &&
          disp_from_frontend.inst[p_idx].rd_regidx == disp_from_frontend.inst[d_idx].rs2_regidx) begin
        rs2_rnid_tmp_valid[p_idx] = 1'b1;
        rs2_rnid_tmp[p_idx] = w_rd_rnid[p_idx];
      end else begin
        rs2_rnid_tmp_valid[p_idx] = rs2_rnid_tmp_valid[p_idx-1];
        rs2_rnid_tmp      [p_idx] = rs2_rnid_tmp      [p_idx-1];
      end // else: !if(disp_from_frontend.inst[p_idx].rd_valid &&...
    end // block: prev_rd_loop

  end // always_comb

  /* verilator lint_off SELRANGE */
  assign rs1_rnid_fwd[d_idx] = (d_idx == 0) ? w_rnid[0] : rs1_rnid_tmp[d_idx-1];
  assign rs2_rnid_fwd[d_idx] = (d_idx == 0) ? w_rnid[1] : rs2_rnid_tmp[d_idx-1];

  assign w_disp_inst[d_idx] = msrh_pkg::assign_disp_rename (disp_from_frontend.inst[d_idx],
                                                            w_rd_rnid[d_idx],
                                                            w_active [d_idx*2+0],
                                                            rs1_rnid_fwd[d_idx],
                                                            w_active [d_idx*2+1],
                                                            rs2_rnid_fwd[d_idx]);

end // block: src_rn_loop
endgenerate


endmodule // msrh_rename
