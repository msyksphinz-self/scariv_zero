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

 vlvtype_upd_if.slave vlvtype_upd_if
 );

typedef logic [VLVTYPE_REN_SIZE-1: 0] vlvtype_ren_size_t;

vlvtype_t r_vlvtype_table[VLVTYPE_REN_SIZE];
vlvtype_ren_size_t r_table_valid;
vlvtype_ren_size_t r_table_ready;

vlvtype_ren_idx_t r_head_ptr;
vlvtype_ren_idx_t r_tail_ptr;
vlvtype_ren_idx_t w_vlvtype_restore_index;
vlvtype_ren_idx_t r_curr_index;

logic                                 w_commit_flush;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_head_ptr <= 'h0;
    r_curr_index <= 'h0;
  end else begin
    if (w_commit_flush) begin
      r_head_ptr   <= 'h0;
      r_curr_index <= 'h0;
    end else if (br_upd_if.update & ~br_upd_if.dead & br_upd_if.mispredict) begin
      r_head_ptr   <= w_vlvtype_restore_index;
      r_curr_index <= w_vlvtype_restore_index - 1;
    end else if (vlvtype_req_if.valid & !vlvtype_req_if.full) begin
      r_head_ptr <= r_head_ptr + 1;
      r_curr_index <= r_head_ptr;
    end

    if (w_commit_flush) begin
      r_tail_ptr <= 'h0;
    end else if (vlvtype_commit_if.valid) begin
      r_tail_ptr <= r_tail_ptr + 1;
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
    r_table_ready <= 'h0;
    r_table_valid <= 'h0;
  end else begin
    if (w_commit_flush) begin
      r_table_ready <= 'h0;
      r_table_valid <= 'h0;
    end else begin
      if (vlvtype_commit_if.valid) begin
        r_table_valid[r_tail_ptr] <= 1'b0;
        r_table_ready[r_tail_ptr] <= 1'b0;
      end
      if (vlvtype_req_if.valid & !vlvtype_req_if.full) begin
        r_table_valid[r_head_ptr] <= 1'b1;
        r_table_ready[r_head_ptr] <= 1'b0;
      end

      if (vlvtype_upd_if.valid) begin
        r_table_ready  [vlvtype_upd_if.index] <= 1'b1;
        r_vlvtype_table[vlvtype_upd_if.index] <= vlvtype_upd_if.vlvtype;
      end
    end // else: !if(w_commit_flush)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign w_commit_flush = is_flushed_commit(i_commit);

scariv_vec_vlvtype_snapshots
u_snapshots
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_load          (vlvtype_req_if.checkpt_push_valid),
   .i_brtag         (i_brtag),
   .i_vlvtype_index (r_head_ptr),

   .br_upd_if (br_upd_if),

   .o_vlvtype_index (w_vlvtype_restore_index)
   );


endmodule // scariv_vec_vlvtype_rename
