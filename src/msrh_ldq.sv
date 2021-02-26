module msrh_ldq
  (
    input logic i_clk,
    input logic i_reset_n,

    input logic         [msrh_pkg::DISP_SIZE-1:0] i_disp_valid,
    disp_if.slave                                 disp
   );

typedef enum                                      logic[1:0] { INIT = 0, RUN = 1, LMQ_HAZ = 2, STQ_HAZ = 3 } state_t;

typedef struct packed {
logic          is_valid;
logic          is_active;
logic [msrh_pkg::CMT_BLK_W-1:0] cmt_id;
logic [msrh_pkg::DISP_SIZE-1:0] grp_id;
  state_t state;
logic [riscv_pkg::VADDR_W-1: 0] vaddr;

} ldq_entry_t;

function ldq_entry_t assign_ldq_disp (msrh_pkg::disp_t in,
                                      logic [msrh_pkg::CMT_BLK_W-1: 0] cmt_id,
                                      logic [msrh_pkg::DISP_SIZE-1: 0] grp_id);
  ldq_entry_t ret;

  ret.is_valid  = 1'b1;
  ret.cmt_id    = cmt_id;
  ret.grp_id    = grp_id;
  ret.state     = INIT;
  ret.vaddr     = 'h0;
  ret.is_active = 1'b0;

  return ret;
endfunction // assign_ldq_disp


ldq_entry_t r_ldq_entries[msrh_lsu_pkg::LDQ_SIZE];

msrh_pkg::disp_t disp_picked_inst[msrh_pkg::MEM_DISP_SIZE];
logic [msrh_pkg::MEM_DISP_SIZE-1:0] disp_picked_inst_valid;
logic [msrh_pkg::DISP_SIZE-1:0] disp_picked_grp_id[msrh_pkg::MEM_DISP_SIZE];

msrh_disp_pickup
  #(
    .PORT_BASE(0),
    .PORT_SIZE(msrh_pkg::MEM_DISP_SIZE)
    )
u_msrh_disp_pickup
  (
   .i_disp_valid (i_disp_valid),
   .i_disp (disp),

   .o_disp_valid  (disp_picked_inst_valid),
   .o_disp        (disp_picked_inst),
   .o_disp_grp_id (disp_picked_grp_id)
   );

//
// LDQ Pointer
//
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0] w_in_ptr;
logic [$clog2(msrh_pkg::LRQ_ENTRY_SIZE)-1:0] w_out_ptr;
logic                                        w_in_vld;
logic                                        w_out_vld;
logic [msrh_pkg::LRQ_ENTRY_SIZE-1:0]         w_load_valid;

assign w_in_vld  = |w_load_valid;
assign w_out_vld = o_l1d_ext_req.valid;

inoutptr #(.SIZE(msrh_pkg::LRQ_ENTRY_SIZE)) u_req_ptr(.i_clk (i_clk), .i_reset_n(i_reset_n),
                                                      .i_in_vld (w_in_vld ), .o_in_ptr (w_in_ptr ),
                                                      .i_out_vld(w_out_vld), .o_out_ptr(w_out_ptr));

generate for (genvar l_idx = 0; l_idx < msrh_lsu_pkg::LDQ_SIZE; l_idx++) begin : ldq_loop
  logic [msrh_pkg::MEM_DISP_SIZE-1: 0]  w_input_valid;
  msrh_pkg::disp_t           w_disp_entry;
  logic [msrh_pkg::DISP_SIZE-1: 0] w_disp_grp_id;
  for (genvar i_idx = 0; i_idx < msrh_pkg::MEM_DISP_SIZE; i_idx++) begin : in_loop
    assign w_input_valid[i_idx] = i_disp_valid[i_idx] & (w_out_ptr + i_idx == l_idx);
  end

  bit_oh_or #(.WIDTH($size(msrh_pkg::disp_t)), .WORDS(msrh_pkg::MEM_DISP_SIZE)) bit_oh_entry  (.i_oh(w_input_valid), .i_data(i_disp_info), .o_selected(w_disp_entry));
  bit_oh_or #(.WIDTH(msrh_pkg::DISP_SIZE),     .WORDS(msrh_pkg::MEM_DISP_SIZE)) bit_oh_grp_id (.i_oh(w_input_valid), .i_data(i_grp_id), .o_selected(w_disp_grp_id));

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_ldq_entries[l_idx] <= 'h0;
    end else begin
      if (w_in_vld) begin
        r_ldq_entries[l_idx] <= assign_ldq_disp(w_disp_entry, disp.cmt_id, w_disp_grp_id);
      end
    end
  end

end
endgenerate

endmodule // msrh_ldq
