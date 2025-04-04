// ------------------------------------------------------------------------
// NAME : scariv_snoop_top
// TYPE : module
// ------------------------------------------------------------------------
// Snoop Unit
//  Get Request from External and snooping inside CPU core
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

module scariv_snoop_top
  import scariv_lsu_pkg::*;
  (
    input logic i_clk,
    input logic i_reset_n,

   // Cache Coherent Interface
   snoop_if.slave snoop_if,

   // Snoop Information
   snoop_info_if.master snoop_info_if,

   // Internal Broadcast Interface
   stq_snoop_if.master   stq_snoop_if,
   mshr_snoop_if.master  mshr_snoop_if,
   l1d_snoop_if.master   l1d_snoop_if,
   stbuf_snoop_if.master stbuf_snoop_if,
   streq_snoop_if.master streq_snoop_if
   );

  typedef enum logic [ 1: 0] {
     IDLE = 0,
     WAIT_RESP = 1,
     WAIT_HAZ_RESOLVE = 2,
     INVALIDATE_L1D_LINE = 3
  } state_t;

  typedef enum logic [ 2: 0] {
    L1D_INDEX = 0,
    STQ_INDEX = 1,
    MSHR_INDEX = 2,
    STBUF_INDEX = 3,
    STREQ_INDEX = 4,
    MAX_INDEX   = 5
  } resp_index_t;

logic [MAX_INDEX-1: 0] r_resp_valid;

state_t                                      r_l1d_state;
scariv_pkg::paddr_t                          r_l1d_paddr;
logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]  r_l1d_data;
logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0] r_l1d_be;

state_t                                      r_stq_state;
logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]  r_stq_data;
logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0] r_stq_be;

state_t                                      r_mshr_state;
logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]  r_mshr_data;
logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0] r_mshr_be;
logic [scariv_conf_pkg::MISSU_ENTRY_SIZE-1: 0] r_mshr_haz_entry_index;
logic                                          w_mshr_haz_solved;

assign w_mshr_haz_solved = ((r_mshr_haz_entry_index & mshr_snoop_if.entry_valid) == 'h0) |
                           |(r_mshr_haz_entry_index & mshr_snoop_if.entry_resolved);

state_t                                      r_stbuf_state;
logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]  r_stbuf_data;
logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0] r_stbuf_be;

state_t                                      r_streq_state;
logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0]  r_streq_data;
logic [scariv_lsu_pkg::DCACHE_DATA_B_W-1: 0] r_streq_be;

logic                  w_snoop_if_fire;
assign w_snoop_if_fire = snoop_if.req_valid/* & snoop_if.resp_ready*/;

logic                  r_snoop_busy;

assign snoop_info_if.busy = r_snoop_busy;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_snoop_busy <= 1'b0;

    l1d_snoop_if.req_s0_valid <= 1'b0;
    stq_snoop_if.req_s0_valid <= 1'b0;

    r_l1d_state   <= IDLE;
    r_stq_state   <= IDLE;
    r_mshr_state  <= IDLE;
    r_stbuf_state <= IDLE;
    r_streq_state <= IDLE;

    r_resp_valid <= 'h0;
  end else begin
    if (!r_snoop_busy & w_snoop_if_fire) begin
      r_snoop_busy <= 1'b1;
    end else if (r_snoop_busy & (r_l1d_state == IDLE)) begin
      r_snoop_busy <= 1'b0;
    end

    // L1D state machine
    case (r_l1d_state)
      IDLE : begin
        if (w_snoop_if_fire) begin
          r_l1d_state <= WAIT_RESP;
          r_resp_valid[L1D_INDEX]   <= 1'b0;
          l1d_snoop_if.req_s0_valid <= 1'b1;
          l1d_snoop_if.req_s0_cmd   <= SNOOP_READ;
          l1d_snoop_if.req_s0_paddr <= {snoop_if.req_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)], {$clog2(DCACHE_DATA_B_W){1'b0}}};
          r_l1d_paddr               <= {snoop_if.req_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)], {$clog2(DCACHE_DATA_B_W){1'b0}}};
        end else if ((r_mshr_state == WAIT_HAZ_RESOLVE) & w_mshr_haz_solved) begin
          r_l1d_state               <= WAIT_RESP;
          r_resp_valid[L1D_INDEX]   <= 1'b0;
          l1d_snoop_if.req_s0_valid <= 1'b1;
          l1d_snoop_if.req_s0_cmd   <= SNOOP_READ;
          l1d_snoop_if.req_s0_paddr <= r_l1d_paddr;
        end
      end // case: IDLE
      WAIT_RESP : begin
        if (l1d_snoop_if.resp_s1_valid) begin
          if (l1d_snoop_if.resp_s1_status == STATUS_L1D_CONFLICT) begin
            // L1D conflicted, replay
            l1d_snoop_if.req_s0_valid <= 1'b1;
          end else begin
            if (l1d_snoop_if.resp_s1_status == STATUS_HIT) begin
              r_l1d_state <= INVALIDATE_L1D_LINE;
              l1d_snoop_if.req_s0_valid <= 1'b1;
              l1d_snoop_if.req_s0_cmd <= SNOOP_INVALID;
              l1d_snoop_if.req_s0_ways <= l1d_snoop_if.resp_s1_ways;
            end else begin
              r_l1d_state <= IDLE;
              r_resp_valid[L1D_INDEX]   <= 1'b1;
            end

            r_l1d_data <= l1d_snoop_if.resp_s1_data;
            r_l1d_be   <= l1d_snoop_if.resp_s1_status == STATUS_HIT ?
                          {DCACHE_DATA_B_W{1'b1}} :
                          {DCACHE_DATA_B_W{1'b0}};
          end
        end else begin
          l1d_snoop_if.req_s0_valid <= 1'b0;
        end
      end // case: WAIT_RESP
      INVALIDATE_L1D_LINE : begin
        if (l1d_snoop_if.resp_s1_valid) begin
          if (l1d_snoop_if.resp_s1_status == STATUS_L1D_CONFLICT) begin
            // L1D conflicted, replay
            l1d_snoop_if.req_s0_valid <= 1'b1;
          end else begin
            r_l1d_state <= IDLE;
            r_resp_valid[L1D_INDEX] <= 1'b1;
          end
        end else begin
          l1d_snoop_if.req_s0_valid <= 1'b0;
        end // else: !if(l1d_snoop_if.resp_s1_valid)
      end // case: INVALIDATE_L1D_LINE
      default : begin
`ifdef SIMULATION
        $fatal(0, "default state reached.");
`endif // SIMULATION
      end
    endcase // case (r_l1d_state)

    // STQ state machine
    case (r_stq_state)
      IDLE : begin
        if (w_snoop_if_fire) begin
          r_resp_valid[STQ_INDEX] <= 1'b0;
          r_stq_state <= WAIT_RESP;
          stq_snoop_if.req_s0_valid <= 1'b1;
          stq_snoop_if.req_s0_paddr <= {snoop_if.req_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)], {$clog2(DCACHE_DATA_B_W){1'b0}}};
        end
      end
      WAIT_RESP : begin
        stq_snoop_if.req_s0_valid <= 1'b0;
        if (stq_snoop_if.resp_s1_valid) begin
          r_stq_state <= IDLE;
          r_resp_valid[STQ_INDEX] <= 1'b1;
          r_stq_data <= stq_snoop_if.resp_s1_data;
          r_stq_be   <= stq_snoop_if.resp_s1_be;
        end
      end
      default : begin
`ifdef SIMULATION
        $fatal(0, "default state reached.");
`endif // SIMULATION
      end
    endcase // case (r_state)

    // MSHR state machine
    case (r_mshr_state)
      IDLE : begin
        if (w_snoop_if_fire) begin
          r_resp_valid[MSHR_INDEX] <= 1'b0;
          r_mshr_state <= WAIT_RESP;
          mshr_snoop_if.req_s0_valid <= 1'b1;
          mshr_snoop_if.req_s0_paddr <= {snoop_if.req_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)], {$clog2(DCACHE_DATA_B_W){1'b0}}};
        end
      end
      WAIT_RESP : begin
        if (mshr_snoop_if.resp_s1_valid) begin
          mshr_snoop_if.req_s0_valid <= 1'b0;
          if (mshr_snoop_if.resp_s1_hit_index != 'h0 &&
              !mshr_snoop_if.resp_s1_evict_valid) begin
            r_mshr_state           <= WAIT_HAZ_RESOLVE;
            r_mshr_haz_entry_index <= mshr_snoop_if.resp_s1_hit_index;
            r_mshr_be    <= 'h0;
          end else begin
            r_resp_valid[MSHR_INDEX]   <= 1'b1;
            r_mshr_state <= IDLE;
            r_mshr_data  <= mshr_snoop_if.resp_s1_data;
            r_mshr_be    <= mshr_snoop_if.resp_s1_be;
          end
        end // if (mshr_snoop_if.resp_s1_valid)
      end // case: WAIT_RESP
      WAIT_HAZ_RESOLVE : begin
        if (w_mshr_haz_solved) begin
          r_mshr_state <= IDLE;
          r_resp_valid[MSHR_INDEX] <= 1'b1;
          r_mshr_haz_entry_index <= 'h0;
        end
      end
      default : begin
`ifdef SIMULATION
        $fatal(0, "default state reached.");
`endif // SIMULATION
      end
    endcase // case (r_state)

    // STBUF state machine
    case (r_stbuf_state)
      IDLE : begin
        if (w_snoop_if_fire) begin
          r_resp_valid[STBUF_INDEX] <= 1'b0;
          r_stbuf_state <= WAIT_RESP;
          stbuf_snoop_if.req_s0_valid <= 1'b1;
          stbuf_snoop_if.req_s0_paddr <= {snoop_if.req_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)], {$clog2(DCACHE_DATA_B_W){1'b0}}};
        end
      end
      WAIT_RESP : begin
        stbuf_snoop_if.req_s0_valid <= 1'b0;
        if (stbuf_snoop_if.resp_s1_valid) begin
          r_stbuf_state <= IDLE;
          r_resp_valid[STBUF_INDEX] <= 1'b1;
          r_stbuf_data <= stbuf_snoop_if.resp_s1_data;
          r_stbuf_be   <= stbuf_snoop_if.resp_s1_be;
        end
      end
      default : begin
`ifdef SIMULATION
        $fatal(0, "default state reached.");
`endif // SIMULATION
      end
    endcase // case (r_state)


    // STREQ state machine
    case (r_streq_state)
      IDLE : begin
        if (w_snoop_if_fire) begin
          r_resp_valid[STREQ_INDEX] <= 1'b0;
          r_streq_state <= WAIT_RESP;
          streq_snoop_if.req_s0_valid <= 1'b1;
          streq_snoop_if.req_s0_paddr <= {snoop_if.req_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)], {$clog2(DCACHE_DATA_B_W){1'b0}}};
        end
      end
      WAIT_RESP : begin
        streq_snoop_if.req_s0_valid <= 1'b0;
        if (streq_snoop_if.resp_s1_valid) begin
          r_streq_state <= IDLE;
          r_resp_valid[STREQ_INDEX] <= 1'b1;
          r_streq_data <= streq_snoop_if.resp_s1_data;
          r_streq_be   <= streq_snoop_if.resp_s1_be;
        end
      end
      default : begin
`ifdef SIMULATION
        $fatal(0, "default state reached.");
`endif // SIMULATION
      end
    endcase // case (r_state)


    if (&r_resp_valid) begin
      snoop_if.resp_valid <= 1'b1;
      r_resp_valid <= 'h0;
      for (int b_idx = 0; b_idx < DCACHE_DATA_B_W; b_idx++) begin : byte_loop
        snoop_if.resp_payload.data[b_idx*8 +: 8] <= {8{r_l1d_be  [b_idx]}} & r_l1d_data  [b_idx*8 +: 8] |
                                                    {8{r_stq_be  [b_idx]}} & r_stq_data  [b_idx*8 +: 8] |
                                                    {8{r_mshr_be [b_idx]}} & r_mshr_data [b_idx*8 +: 8] |
                                                    {8{r_stbuf_be[b_idx]}} & r_stbuf_data[b_idx*8 +: 8] |
                                                    {8{r_streq_be[b_idx]}} & r_streq_data[b_idx*8 +: 8] ;
        snoop_if.resp_payload.be  [b_idx       ] <= r_l1d_be[b_idx] | r_stq_be[b_idx];
      end
    end else begin
      snoop_if.resp_valid <= 1'b0;
    end
  end
end

endmodule // scariv_snoop_top
