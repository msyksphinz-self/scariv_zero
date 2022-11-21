module scariv_disp_pickup
  #(
    parameter PORT_BASE = 0,
    parameter STRIDE    = 1,
    parameter PORT_SIZE = 2
    )
(
 input scariv_pkg::grp_id_t  i_disp_valid,
 disp_if.watch                          i_disp,

 output logic [PORT_SIZE-1:0]           o_disp_valid,
 output scariv_pkg::disp_t                o_disp[PORT_SIZE],
 output scariv_pkg::grp_id_t o_disp_grp_id[PORT_SIZE]
 );

scariv_pkg::disp_t w_disp_inst[scariv_conf_pkg::DISP_SIZE];
generate for(genvar d_idx = 0; d_idx < scariv_conf_pkg::DISP_SIZE; d_idx++) begin : d_loop
  assign w_disp_inst[d_idx] = i_disp.inst[d_idx];
end
endgenerate

generate
  for (genvar p_idx = 0; p_idx < PORT_SIZE; p_idx++) begin : pick_loop
    bit_pick_1_index #(
        .NUM(PORT_BASE + STRIDE * p_idx),
        .SEL_WIDTH(scariv_conf_pkg::DISP_SIZE),
        .DATA_WIDTH($size(scariv_pkg::disp_t))
    ) u_bit_pick_1_index (
        .i_valids     (i_disp_valid),
        .i_data       (w_disp_inst),
        .o_valid      (o_disp_valid [p_idx]),
        .o_data       (o_disp       [p_idx]),
        .o_picked_pos (o_disp_grp_id[p_idx])
    );
  end  // block: d_loop
endgenerate

endmodule // scariv_disp_pickup
