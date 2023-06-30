// ------------------------------------------------------------------------
// NAME : scariv_lsu_replay_queue
// TYPE : module
// ------------------------------------------------------------------------
// LSU Replay Queue
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_lsu_replay_queue
  import scariv_lsu_pkg::*;
(
    input logic i_clk,
    input logic i_reset_n,

    input logic           i_ex2_mispred_valid,
    input ex2_q_update_t  i_ex2_mispred_info,

    output logic          o_full,

    // Request from Replay Queue
    lsu_replay_if.master lsu_replay_if,

);

localparam REPLAY_QUEUE_SIZE = (LDQ_SIZE + STQ_SIZE) / 2;
localparam REPLAY_QUEUE_W = $clog2(REPLAY_QUEUE_SIZE);

typedef logic [REPLAY_QUEUE_W-1: 0] replay_queue_idx_t;
replay_queue_idx_t r_head_ptr;
replay_queue_idx_t r_tail_ptr;
replay_queue_idx_t w_head_ptr_next;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
        r_head_ptr <= 'h0;
        r_tail_ptr <= 'h0;
    end else begin
        if (i_ex2_mispred_valid) begin
            r_head_ptr <= w_head_ptr_next;
        end
        if (lsu_replay_if.valid & lsu_replay_if.ready) begin
            r_tail_ptr <= r_tail_ptr + 'h1;
        end
    end
end

data_array_1p
#(
    .WIDTH($clog2(REPLAY_QUEUE_SIZE)),
    .ADDR_W()
)
u_replay_queue
(
    .i_clk(),
    .i_reset_n(),
    .i_wr(),
    .i_addr(),
    .i_data()

    .o_data(),
)

assign w_head_ptr_next = r_head_ptr + 'h1;

assign o_full = w_head_ptr_next == r_tail_ptr;

endmodule
