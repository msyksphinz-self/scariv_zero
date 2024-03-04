module scariv_stq_rs2_rel_pipe
  import scariv_lsu_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 input logic                     i_ex0_rel_valid,
 input scariv_pkg::rel_bus_idx_t i_ex0_rel_idx,
 input scariv_pkg::rnid_t        i_ex0_rnid,
 input scariv_pkg::reg_t         i_ex0_type,

 output logic                    o_ex1_rel_valid,
 output scariv_pkg::alen_t       o_ex1_rel_data,
 output logic                    o_ex1_mispredicted,

 input logic [scariv_conf_pkg::STQ_SIZE-1: 0]          i_ex0_stq_valid,
 output logic [$clog2(scariv_conf_pkg::STQ_SIZE)-1: 0] o_ex1_stq_ptr,

 // Physical Register Write Interface
 lsu_mispred_if.slave mispred_in_if [scariv_conf_pkg::LSU_INST_NUM],
 phy_wr_if.slave      phy_wr_in_if  [scariv_pkg::TGT_BUS_SIZE]
 );

// ------------
// Bypass Read
// ------------
logic                            w_ex0_mispredicted;

logic                            r_ex1_rel_valid;
scariv_pkg::rel_bus_idx_t        r_ex1_rel_idx;
scariv_pkg::rnid_t               r_ex1_rnid;
scariv_pkg::reg_t                r_ex1_type;

select_mispred_bus  rs_mispred_select(.i_entry_rnid (i_ex0_rnid), .i_entry_type (i_ex0_type), .i_mispred  (mispred_in_if),
                                      .o_mispred    (w_ex0_mispredicted));

logic [$clog2(scariv_conf_pkg::STQ_SIZE)-1: 0] w_ex0_stq_ptr;
bit_encoder #(.WIDTH(scariv_conf_pkg::STQ_SIZE)) u_encoder_ptr (.i_in(i_ex0_stq_valid), .o_out(w_ex0_stq_ptr));

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ex1_rel_valid <= 1'b0;
  end else begin
    r_ex1_rel_valid <= i_ex0_rel_valid;
    r_ex1_rel_idx   <= i_ex0_rel_idx  ;

    o_ex1_rel_valid    <= i_ex0_rel_valid;
    o_ex1_stq_ptr      <= w_ex0_stq_ptr;
    o_ex1_mispredicted <= w_ex0_mispredicted;
  end
end

scariv_pkg::alen_t w_ex1_tgt_data [scariv_pkg::TGT_BUS_SIZE];
for (genvar tgt_idx = 0; tgt_idx < scariv_pkg::TGT_BUS_SIZE; tgt_idx++) begin : rs_tgt_loop
  assign w_ex1_tgt_data[tgt_idx] = phy_wr_in_if[tgt_idx].rd_data;
end
assign o_ex1_rel_data = w_ex1_tgt_data[r_ex1_rel_idx];

endmodule // scariv_stq_rs2_rel_pipe
