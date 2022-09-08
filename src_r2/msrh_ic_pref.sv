// ------------------------------------------------------------------------
// NAME : MRSH Frontend Instruction Prefetcher
// TYPE : module
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------

module msrh_ic_pref
  import msrh_pkg::*;
  import msrh_ic_pkg::*;
  import msrh_lsu_pkg::*;
(
 input logic i_clk,
 input logic i_reset_n,

 input logic i_flush_valid,
 input logic i_fence_i,

 // Interface accessing with L2 by normal i-fetch
 input logic    i_ic_l2_req_fire,
 input paddr_t  i_ic_l2_req_paddr,

 // Requests prefetch
 output logic   o_pref_l2_req_valid,
 input logic    i_pref_l2_req_ready,
 output paddr_t o_pref_l2_req_paddr,

 // Response prefetech
 input logic     i_pref_l2_resp_valid,
 input ic_data_t i_pref_l2_resp_data,

 // Instruction Fetch search
 input logic      i_s1_pref_search_valid,
 input vaddr_t    i_s1_pref_search_vaddr,
 input paddr_t    i_s1_pref_search_paddr,
 output logic     o_s2_pref_search_hit,
 output ic_data_t o_s2_pref_search_data,

 // Write ICCache Interface
 output logic     o_ic_wr_valid,
 input  logic     i_ic_wr_ready,
 output vaddr_t   o_ic_wr_vaddr,
 output ic_data_t o_ic_wr_data
 );

// Prefetcher state machine
ic_state_t        r_pref_state;
msrh_pkg::paddr_t r_pref_paddr;
ic_ways_idx_t     r_pref_replace_way;
msrh_pkg::vaddr_t r_pref_waiting_vaddr;

logic     r_pref_l2_valid;
paddr_t   r_pref_l2_paddr;
ic_data_t r_pref_l2_data;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_pref_state <= ICInit;
  end else begin
    case (r_pref_state)
      ICInit : begin
        if (~i_flush_valid & i_ic_l2_req_fire & !i_fence_i) begin
          r_pref_state <= ICReq;
          r_pref_paddr <= i_ic_l2_req_paddr + msrh_conf_pkg::ICACHE_DATA_W / 8;
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
  end else begin
    if ((r_pref_state == ICResp) & i_pref_l2_resp_valid) begin
      r_pref_l2_valid <= 1'b1;
      r_pref_l2_paddr <= r_pref_paddr;
      r_pref_l2_data  <= i_pref_l2_resp_data;
    end else if (o_ic_wr_valid & i_ic_wr_ready) begin
      r_pref_l2_valid <= 1'b0;
    end
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


logic w_s1_pref_search_hit;
assign w_s1_pref_search_hit = i_s1_pref_search_valid &
                              r_pref_l2_valid &
                              (i_s1_pref_search_paddr[$clog2(msrh_conf_pkg::ICACHE_DATA_W)-1: $clog2(ICACHE_DATA_B_W)] ==
                               r_pref_l2_paddr[$clog2(msrh_conf_pkg::ICACHE_DATA_W)-1: $clog2(ICACHE_DATA_B_W)]);

always_ff @ (posedge i_clk) begin
  // Search
  o_s2_pref_search_hit  <= w_s1_pref_search_hit;
  o_s2_pref_search_data <= r_pref_l2_data;
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
        if (w_s1_pref_search_hit) begin
          r_pref_search_vaddr <= i_s1_pref_search_vaddr;
          r_pref_wr_state <= PrefWrWait;
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
assign o_ic_wr_vaddr = r_pref_search_vaddr;
assign o_ic_wr_data  = r_pref_l2_data;

endmodule // msrh_ic_pref
