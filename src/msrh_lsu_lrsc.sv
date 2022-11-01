// ------------------------------------------------------------------------
// NAME : MSRH LR/SC Buffer
// TYPE : module
// ------------------------------------------------------------------------
// LR/SC Information
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_lsu_lrsc
  (
   input logic i_clk,
   input logic i_reset_n,

   lrsc_if.slave lrsc_if[msrh_conf_pkg::LSU_INST_NUM]
   );

logic                   r_lr_registered_valid;
msrh_pkg::paddr_t       r_lr_paddr;

logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_lr_update_valids;
logic [msrh_conf_pkg::LSU_INST_NUM-1: 0] w_sc_check_valids;

msrh_pkg::paddr_t w_lrsc_paddr_array [msrh_conf_pkg::LSU_INST_NUM];
msrh_pkg::paddr_t w_lr_paddr_sel;
msrh_pkg::paddr_t w_sc_paddr_sel;

/* verilator lint_off UNOPTFLAT */
logic                                    w_sc_success;

generate for (genvar p_idx = 0; p_idx < msrh_conf_pkg::LSU_INST_NUM; p_idx++) begin : lsu_port_loop
  assign w_lr_update_valids[p_idx] = lrsc_if[p_idx].lr_update_valid;
  assign w_sc_check_valids [p_idx] = lrsc_if[p_idx].sc_check_valid;

  assign w_lrsc_paddr_array[p_idx] = lrsc_if[p_idx].paddr;
  assign lrsc_if[p_idx].sc_success = w_sc_success;
end
endgenerate

bit_oh_or
  #(.T(msrh_pkg::paddr_t), .WORDS(msrh_conf_pkg::LSU_INST_NUM))
u_lr_addr_sel
  (.i_oh(w_lr_update_valids), .i_data(w_lrsc_paddr_array), .o_selected(w_lr_paddr_sel));


bit_oh_or
  #(.T(msrh_pkg::paddr_t), .WORDS(msrh_conf_pkg::LSU_INST_NUM))
u_sc_addr_sel
  (.i_oh(w_sc_check_valids), .i_data(w_lrsc_paddr_array), .o_selected(w_sc_paddr_sel));


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_lr_registered_valid <= 1'b0;
    r_lr_paddr <= 'h0;
  end else begin
    if (|w_lr_update_valids) begin
      r_lr_registered_valid <= 1'b1;
      r_lr_paddr <= w_lr_paddr_sel;
    end else if (|w_sc_check_valids) begin
      r_lr_registered_valid <= 1'b0;
    end
  end
end

assign w_sc_success = r_lr_registered_valid & (r_lr_paddr == w_sc_paddr_sel);

endmodule; // msrh_lsu_lrsc
