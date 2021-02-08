module mrh_tile
(
    input logic i_clk,
    input logic i_reset_n,

    // L2 request from ICache
    l2_req_if.master ic_l2_req,
    l2_resp_if.slave ic_l2_resp
);

l2_req_if  l2_req  ();
l2_resp_if l2_resp ();

disp_if    disp_from_frontend ();
disp_if    disp_from_decoder ();
disp_if    disp_to_scheduler ();

logic [mrh_pkg::DISP_SIZE-1: 0] w_disp_valids;

frontend u_frontend
(
    .i_clk (i_clk),
    .i_reset_n (i_reset_n),

    .ic_l2_req  (ic_l2_req ),
    .ic_l2_resp (ic_l2_resp),

    .disp (disp_from_frontend)
);

mrh_decoder u_decoder
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .disp_from_frontend (disp_from_frontend),
   .disp_to_renamer  (disp_from_decoder)
   );


mrh_rename u_rename
  (
   .i_clk (i_clk),
   .i_reset_n (i_reset_n),

   .disp_from_frontend (disp_from_decoder),
   .disp_to_scheduler (disp_to_scheduler)
   );


generate for (genvar d_idx = 0; d_idx < mrh_pkg::DISP_SIZE; d_idx++) begin : disp_vld_loop
  assign w_disp_valids[d_idx] = disp_to_scheduler.inst[d_idx].valid;
end
endgenerate

generate for (genvar alu_idx = 0; alu_idx < mrh_pkg::ALU_INST_NUM; alu_idx++) begin : alu_loop
  mrh_alu
                               #(
                                 .PORT_BASE (alu_idx * 2)
                                 )
  u_mrh_alu
                               (
                                .i_clk(i_clk),
                                .i_reset_n(i_reset_n),

                                .disp_valid(w_disp_valids),
                                .disp(disp_to_scheduler)
                                );
end
endgenerate

endmodule // mrh_tile
