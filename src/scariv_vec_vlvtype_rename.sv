// ------------------------------------------------------------------------
// NAME : SCARIV VLVTYPE Rename
// TYPE : module
// ------------------------------------------------------------------------
// Rename Unit
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_vec_vlvtype_rename
  import scariv_pkg::*;
  import scariv_vec_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 vlvtype_req_if.slave    vlvtype_req_if,
 vlvtype_commit_if.slave vlvtype_commit_if,
 input brtag_t           i_brtag,

 input commit_blk_t   i_commit,
 // Branch Tag Update Signal
 br_upd_if.slave      br_upd_if,

 // From CSU pipeline
 vec_csr_if.slave     vec_csr_if,
 vlvtype_upd_if.slave vlvtype_upd_if
 );

typedef logic [VLVTYPE_REN_SIZE-1: 0] vlvtype_ren_size_t;

vlvtype_t r_vlvtype_table[VLVTYPE_REN_SIZE];
vlvtype_ren_size_t r_table_valid;
vlvtype_ren_size_t r_table_ready;

vlvtype_ren_idx_t r_head_ptr;
vlvtype_ren_idx_t r_curr_index;
vlvtype_ren_idx_t r_committed_ptr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_ptr      <= 'h1;
    r_curr_index    <= 'h0;
    r_committed_ptr <= 'h0;
  end else begin
    if (vlvtype_req_if.valid & !vlvtype_req_if.full) begin
      r_head_ptr   <= r_head_ptr + 1;
      r_curr_index <= r_head_ptr;
    end

    if (vlvtype_commit_if.valid) begin
      // if (vlvtype_commit_if.dead) begin
      //   r_head_ptr   <= r_committed_ptr + 1;
      //   r_curr_index <= r_committed_ptr;
      // end else begin
      //   r_committed_ptr <= r_committed_ptr + 'h1;
      // end
      r_committed_ptr <= r_committed_ptr + 'h1;
    end
  end
end

assign vlvtype_req_if.ready        = r_table_ready[r_curr_index];
assign vlvtype_req_if.full         = &r_table_valid;
assign vlvtype_req_if.vsetvl_index = r_head_ptr;
assign vlvtype_req_if.index        = r_curr_index;
assign vlvtype_req_if.vlvtype      = r_vlvtype_table[r_curr_index];

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_table_ready <= 'h1;
    r_table_valid <= 'h1;
  end else begin
    if (vlvtype_commit_if.valid) begin
      r_table_valid[r_committed_ptr] <= 1'b0;
      r_table_ready[r_committed_ptr] <= 1'b0;
      if (vlvtype_commit_if.dead) begin
        r_vlvtype_table[r_committed_ptr+1] <= r_vlvtype_table[r_committed_ptr];
      end
    end
    if (vlvtype_req_if.valid & !vlvtype_req_if.full) begin
      r_table_valid[r_head_ptr] <= 1'b1;
      r_table_ready[r_head_ptr] <= 1'b0;
`ifdef SIMULATION
      r_vlvtype_table[vlvtype_upd_if.index].sim_cmt_id <= vlvtype_req_if.sim_cmt_id;
      r_vlvtype_table[vlvtype_upd_if.index].sim_grp_id <= vlvtype_req_if.sim_grp_id;
`endif // SIMULATION
    end

    if (vlvtype_upd_if.valid) begin
      r_table_ready  [vlvtype_upd_if.index] <= 1'b1;
      r_vlvtype_table[vlvtype_upd_if.index] <= vlvtype_upd_if.vlvtype;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign vec_csr_if.vlvtype  = r_vlvtype_table[vec_csr_if.index];


endmodule // scariv_vec_vlvtype_rename
