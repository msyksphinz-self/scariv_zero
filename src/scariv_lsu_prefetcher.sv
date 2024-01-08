// ------------------------------------------------------------------------
// NAME : scariv_lsu_prefetcher
// TYPE : module
// ------------------------------------------------------------------------
// L1D Prefetcher
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_lsu_prefetcher
  import scariv_lsu_pkg::*;
(
 input logic       i_clk,
 input logic       i_reset_n,

 // Prefetcher Interface
 pipe_prefetcher_if.slave  pipe_prefetcher_if[scariv_conf_pkg::LSU_INST_NUM],

 input logic                             i_pref_pipe_ready,
 output scariv_lsu_pkg::lsu_pipe_issue_t o_pref_issue

 );

localparam PC_TAG_LEN = 9;

typedef struct packed {
  logic                valid;
  logic [PC_TAG_LEN:1] pc_tag;
  logic [11: 0]        last_line_offset;
  logic [11: 0]        stride;
  logic [ 1: 0]        confidence;
} ipt_entry_t;

function automatic logic [ 1: 0] inc_confidence(logic [ 1: 0] in);
  return in == 2'b11 ? in : in + 2'b1;
endfunction // inc_confidence

function automatic logic [ 1: 0] dec_confidence(logic [ 1: 0] in);
  return in == 2'b00 ? in : in - 2'b1;
endfunction // inc_confidence

// ------------------------
// IPT search & update
// ------------------------
ipt_entry_t[PREF_IPT_SIZE-1: 0] r_ipt_entry;

generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : pipe_loop
  logic [$clog2(PREF_IPT_SIZE)-1: 0] w_ipt_index;
  logic [11: 0]                      w_diff_stride;
  assign w_ipt_index   = pipe_prefetcher_if[p_idx].pc_vaddr[1 +: $clog2(PREF_IPT_SIZE)];
  assign w_diff_stride = pipe_prefetcher_if[p_idx].vaddr[11: 0] - r_ipt_entry[w_ipt_index].last_line_offset[11: 0];

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
    end else begin
      if (pipe_prefetcher_if[p_idx].valid) begin
        if (!r_ipt_entry[w_ipt_index].valid) begin
          // Entry not valid
          r_ipt_entry[w_ipt_index].valid <= 1'b1;
          if (r_ipt_entry[w_ipt_index].pc_tag != pipe_prefetcher_if[p_idx].pc_vaddr[$clog2(PREF_IPT_SIZE)+1 +: PC_TAG_LEN]) begin
            // PC tag different: Different PC access
            r_ipt_entry[w_ipt_index].pc_tag <= pipe_prefetcher_if[p_idx].pc_vaddr[$clog2(PREF_IPT_SIZE)+1 +: PC_TAG_LEN];
            r_ipt_entry[w_ipt_index].last_line_offset <= pipe_prefetcher_if[p_idx].vaddr[11: 0];
            r_ipt_entry[w_ipt_index].stride <= 'h0;
          end
        end else begin
          // Already allocated
          if (r_ipt_entry[w_ipt_index].pc_tag == pipe_prefetcher_if[p_idx].pc_vaddr[$clog2(PREF_IPT_SIZE)+1 +: PC_TAG_LEN]) begin
            // When PC Hit
            r_ipt_entry[w_ipt_index].last_line_offset <= pipe_prefetcher_if[p_idx].vaddr[11: 0];
            r_ipt_entry[w_ipt_index].stride <= w_diff_stride;
            if (r_ipt_entry[w_ipt_index].stride == w_diff_stride) begin
              r_ipt_entry[w_ipt_index].confidence <= inc_confidence(r_ipt_entry[w_ipt_index].confidence);
            end else begin
              r_ipt_entry[w_ipt_index].confidence <= dec_confidence(r_ipt_entry[w_ipt_index].confidence);
            end
          end else begin
            // PC tag different: Different PC access
            r_ipt_entry[w_ipt_index].pc_tag <= pipe_prefetcher_if[p_idx].pc_vaddr[$clog2(PREF_IPT_SIZE)+1 +: PC_TAG_LEN];
            r_ipt_entry[w_ipt_index].last_line_offset <= pipe_prefetcher_if[p_idx].vaddr[11: 0];
            r_ipt_entry[w_ipt_index].stride <= 'h0;
          end // else: !if(r_ipt_entry[w_ipt_index].pc_tag == pipe_prefetcher_if[p_idx].pc_vaddr[$clog2(PREF_IPT_SIZE)+1 +: PC_TAG_LEN])
        end // else: !if(!r_ipt_entry[w_ipt_index].valid)
      end // if (pipe_prefetcher_if[p_idx].valid)
    end // else: !if(!i_reset_n)
  end // always_ff @ (posedge i_clk, negedge i_reset_n)
end endgenerate // block: pipe_loop

logic                              r_pr1_valid;
logic [$clog2(PREF_IPT_SIZE)-1: 0] r_pr1_updated_index;
scariv_pkg::vaddr_t                r_pr1_vaddr;

typedef enum logic {
  INIT = 0,
  PREF_GEN = 1
} pref_state_t;

localparam NUM_DEGREE = 8;

pref_state_t r_pref_state;
logic [$clog2(NUM_DEGREE)-1: 0] r_pref_degree;
scariv_pkg::vaddr_t r_pref_vaddr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_pr1_valid <= 1'b0;
    r_pref_state <= INIT;
  end else begin
    r_pr1_valid <= pipe_prefetcher_if[0].valid;
    r_pr1_updated_index <= pipe_prefetcher_if[0].pc_vaddr[1 +: $clog2(PREF_IPT_SIZE)];
    r_pr1_vaddr <= pipe_prefetcher_if[0].vaddr;

    case (r_pref_state)
      INIT: begin
        if (r_pr1_valid & (&r_ipt_entry[r_pr1_updated_index].confidence)) begin
          r_pref_state <= PREF_GEN;
          r_pref_degree <= 'h0;
          r_pref_vaddr <= r_pr1_vaddr + r_ipt_entry[r_pr1_updated_index].stride;
        end
      end
      PREF_GEN : begin
        if (r_pref_degree == NUM_DEGREE-1) begin
          r_pref_state <= INIT;
        end else begin
          r_pref_vaddr <= r_pref_vaddr + r_ipt_entry[r_pr1_updated_index].stride;
          r_pref_degree <= r_pref_degree + 'h1;
        end
      end
    endcase // case (r_pref_state)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


scariv_pkg::vaddr_t [15: 0] r_rr_filter;
logic [ 3: 0] r_rr_push_ptr;
logic [15: 0] w_hit_rr_filter;
logic         w_pref_gen_valid;

generate for (genvar rr_idx = 0; rr_idx < 16; rr_idx++) begin : rr_filter_search_loop
  assign w_hit_rr_filter[rr_idx] = r_rr_filter[rr_idx][riscv_pkg::VADDR_W-1: $clog2(scariv_conf_pkg::DCACHE_DATA_W/8)] ==
                                   r_pref_vaddr       [riscv_pkg::VADDR_W-1: $clog2(scariv_conf_pkg::DCACHE_DATA_W/8)];
end endgenerate
assign w_pref_gen_valid = ~|w_hit_rr_filter & (r_pref_state == PREF_GEN);


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_rr_push_ptr <= 'h0;
  end else begin
    if (r_pref_state == PREF_GEN) begin
      if (~|w_hit_rr_filter) begin
        r_rr_push_ptr <= r_rr_push_ptr + 'h1;
        r_rr_filter[r_rr_push_ptr] <= r_pref_vaddr;
      end
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

logic               w_pref_ring_fifo_empty;
logic               w_pref_ring_fifo_pop;
scariv_pkg::vaddr_t w_pref_pipe_vaddr;

assign w_pref_ring_fifo_pop = i_pref_pipe_ready & ~w_pref_ring_fifo_empty;

ring_fifo
  #(
    .T(scariv_pkg::vaddr_t),
    .DEPTH(8)
    )
u_pref_req_fifo
  (
   .i_clk     (i_clk                 ),
   .i_reset_n (i_reset_n             ),
   .i_push    (w_pref_gen_valid      ),
   .i_data    (r_pref_vaddr          ),
   .o_empty   (w_pref_ring_fifo_empty),
   .o_full    (                      ),
   .i_pop     (w_pref_ring_fifo_pop  ),
   .o_data    (w_pref_pipe_vaddr     )
   );


always_comb begin
  o_pref_issue = 'h0;
  if (w_pref_ring_fifo_pop) begin
    o_pref_issue.valid = 1'b1;
    o_pref_issue.paddr = w_pref_pipe_vaddr;
    o_pref_issue.is_prefetch = 1'b1;
  end
end

endmodule // scariv_lsu_prefetcher
