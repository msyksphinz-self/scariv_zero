// ------------------------------------------------------------------------
// NAME : scariv_ic_pref
// TYPE : module
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module scariv_ic_pref
  import scariv_pkg::*;
  import scariv_ic_pkg::*;
  import scariv_lsu_pkg::*;
#(parameter CACHE_DATA_B_W = scariv_conf_pkg::DCACHE_DATA_W/8)  // By default use cache width as bus size (Data Width > Fetch Width)
(
 input logic i_clk,
 input logic i_reset_n,

 input logic i_flush_valid,
 input logic i_fence_i,

 // Interface accessing with L2 by normal i-fetch
 input logic    i_ic_l2_req_fire,
 input vaddr_t  i_ic_l2_req_vaddr,
 input paddr_t  i_ic_l2_req_paddr,

 // Requests prefetch
 output logic   o_pref_l2_req_valid,
 input logic    i_pref_l2_req_ready,
 output paddr_t o_pref_l2_req_paddr,

 // Response prefetech
 input logic     i_pref_l2_resp_valid,
 input dc_data_t i_pref_l2_resp_data,

 // Instruction Fetch search
 input logic      i_f0_pref_search_valid,
 input vaddr_t    i_f0_pref_search_vaddr,
 output logic     o_f1_pref_search_hit,
 output dc_data_t o_f1_pref_search_data,
 output logic     o_f1_pref_search_working_hit, // Currently same address is fetching now, will be come response

 // Write ICCache Interface
 output logic     o_ic_wr_valid,
 input  logic     i_ic_wr_ready,
 output vaddr_t   o_ic_wr_vaddr,
 output dc_data_t o_ic_wr_data
 );

// Prefetcher state machine
ic_state_t    r_pref_state;
paddr_t       r_pref_paddr;
ic_ways_idx_t r_pref_replace_way;
vaddr_t       r_pref_vaddr;

logic     r_prefetched_valid;
vaddr_t   r_prefetched_vaddr;
paddr_t   r_prefetched_paddr;
dc_data_t r_prefetched_data;

logic w_is_exceed_next_page;
assign w_is_exceed_next_page = (i_ic_l2_req_vaddr[11: 0] + CACHE_DATA_B_W) >= 13'h1000;


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_pref_state <= ICInit;
  end else begin
    case (r_pref_state)
      ICInit : begin
        if (~i_flush_valid & i_ic_l2_req_fire & !w_is_exceed_next_page & !i_fence_i) begin
          r_pref_state <= ICReq;
          r_pref_vaddr <= (i_ic_l2_req_vaddr & ~{$clog2(CACHE_DATA_B_W){1'b1}}) + CACHE_DATA_B_W;
          r_pref_paddr <= (i_ic_l2_req_paddr & ~{$clog2(CACHE_DATA_B_W){1'b1}}) + CACHE_DATA_B_W;
        end
      end // case: ICInit
      ICReq : begin
        if (i_pref_l2_req_ready & !i_fence_i) begin
          r_pref_state <= ICResp;
        end else if (i_fence_i) begin
          r_pref_state <= ICInvalidate;
        end
      end
      ICResp : begin
        if (i_pref_l2_resp_valid) begin
          r_pref_state   <= ICInit;
        end else if (i_fence_i) begin
          r_pref_state <= ICInvalidate;
        end
      end
      ICInvalidate: begin
        if (i_pref_l2_resp_valid) begin
          r_pref_state <= ICInit;
        end
      end
      default : begin
      end
    endcase // case (r_pref_state)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


assign o_pref_l2_req_valid = (r_pref_state == ICReq);
assign o_pref_l2_req_paddr = r_pref_paddr;

// Search PAaddr
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_prefetched_valid <= 1'b0;
  end else begin
    if ((r_pref_state == ICResp) & i_pref_l2_resp_valid) begin
      r_prefetched_valid <= 1'b1;
      r_prefetched_vaddr <= r_pref_vaddr;
      r_prefetched_data  <= i_pref_l2_resp_data;
    end else if (o_ic_wr_valid & i_ic_wr_ready) begin
      r_prefetched_valid <= 1'b0;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


logic w_f0_pref_search_hit;
logic w_f0_pref_search_working_hit;
logic w_f0_pref_search_working_hit_and_l2_return;

assign w_f0_pref_search_hit = i_f0_pref_search_valid &
                              r_prefetched_valid &
                              (i_f0_pref_search_vaddr[riscv_pkg::VADDR_W-1: $clog2(CACHE_DATA_B_W)] ==
                               r_prefetched_vaddr    [riscv_pkg::VADDR_W-1: $clog2(CACHE_DATA_B_W)]);

assign w_f0_pref_search_working_hit = i_f0_pref_search_valid &
                                      (r_pref_state == ICResp) &
                                      (i_f0_pref_search_vaddr[riscv_pkg::VADDR_W-1: $clog2(CACHE_DATA_B_W)] ==
                                       r_pref_vaddr          [riscv_pkg::VADDR_W-1: $clog2(CACHE_DATA_B_W)]);

assign w_f0_pref_search_working_hit_and_l2_return = w_f0_pref_search_working_hit & i_pref_l2_resp_valid;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    o_f1_pref_search_hit         <= 1'b0;
    o_f1_pref_search_working_hit <= 1'b0;
  end else begin
    // Search
    o_f1_pref_search_hit         <= w_f0_pref_search_hit | w_f0_pref_search_working_hit_and_l2_return;
    o_f1_pref_search_data        <= w_f0_pref_search_working_hit_and_l2_return ? i_pref_l2_resp_data : r_prefetched_data;
    o_f1_pref_search_working_hit <= w_f0_pref_search_working_hit & ~i_pref_l2_resp_valid;
  end
end

// =========================
//  Write ICCache Interface
// =========================

pref_wr_state_t r_pref_wr_state;
vaddr_t         r_pref_search_vaddr;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_pref_wr_state <= PrefWrInit;
  end else begin
    case (r_pref_wr_state)
      PrefWrInit : begin
        if (w_f0_pref_search_hit) begin
          r_pref_search_vaddr <= i_f0_pref_search_vaddr;
          r_pref_wr_state     <= PrefWrWait;
        end
      end
      PrefWrWait : begin
        if (i_ic_wr_ready) begin
          r_pref_wr_state <= PrefWrInit;
        end
      end
      default : begin
      end
    endcase // case (r_pref_wr_state)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


assign o_ic_wr_valid = (r_pref_wr_state == PrefWrWait);
assign o_ic_wr_vaddr = r_prefetched_vaddr;
assign o_ic_wr_data  = r_prefetched_data;

endmodule // scariv_ic_pref
