module msrh_snoop_top
  import msrh_lsu_pkg::*;
  (
    input logic i_clk,
    input logic i_reset_n,

   // Cache Coherent Interface
   snoop_if.slave snoop_if,

   // Internal Broadcast Interface
   stq_snoop_if.master stq_snoop_if,
   l1d_snoop_if.master l1d_snoop_if
   );

  typedef enum logic [ 1: 0] {
     IDLE = 0,
     WAIT_RESP = 1
  } state_t;

  typedef enum logic [ 0: 0] {
    L1D_INDEX = 0,
    STQ_INDEX = 1
  } resp_index_t;

localparam MAX_INDEX = STQ_INDEX + 1;

state_t                r_l1d_state;
state_t                r_stq_state;
logic [MAX_INDEX-1: 0] r_resp_valid;

logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0]  r_l1d_data;
logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1: 0] r_l1d_be;

logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0]  r_stq_data;
logic [msrh_lsu_pkg::DCACHE_DATA_B_W-1: 0] r_stq_be;

logic                  w_snoop_if_fire;
assign w_snoop_if_fire = snoop_if.req_valid/* & snoop_if.resp_ready*/;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    l1d_snoop_if.req_s0_valid <= 1'b0;
    stq_snoop_if.req_s0_valid <= 1'b0;

    r_l1d_state <= IDLE;
    r_stq_state <= IDLE;

    r_resp_valid <= 'h0;
  end else begin
    // L1D state machine
    case (r_l1d_state)
      IDLE : begin
        if (w_snoop_if_fire) begin
          r_l1d_state <= WAIT_RESP;
          r_resp_valid[L1D_INDEX] <= 1'b0;
          l1d_snoop_if.req_s0_valid <= 1'b1;
          l1d_snoop_if.req_s0_paddr <= {snoop_if.req_payload.paddr[riscv_pkg::PADDR_W-1:$clog2(DCACHE_DATA_B_W)], {$clog2(DCACHE_DATA_B_W){1'b0}}};
        end
      end
      WAIT_RESP : begin
        if (l1d_snoop_if.resp_s1_valid) begin
          if (l1d_snoop_if.resp_s1_status == STATUS_L1D_CONFLICT) begin
            // L1D conflicted, replay
            l1d_snoop_if.req_s0_valid <= 1'b1;
          end else begin
            r_l1d_state <= IDLE;
            l1d_snoop_if.req_s0_valid <= 1'b0;
            r_resp_valid[L1D_INDEX] <= 1'b1;

            r_l1d_data <= l1d_snoop_if.resp_s1_data;
            r_l1d_be   <= l1d_snoop_if.resp_s1_status == STATUS_HIT ?
                          {DCACHE_DATA_B_W{1'b1}} :
                          {DCACHE_DATA_B_W{1'b0}};
          end
        end else begin
          l1d_snoop_if.req_s0_valid <= 1'b0;
        end
      end
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

    if (&r_resp_valid) begin
      snoop_if.resp_valid <= 1'b1;
      r_resp_valid <= 'h0;
      for (int b_idx = 0; b_idx < DCACHE_DATA_B_W; b_idx++) begin : byte_loop
        snoop_if.resp_payload.data[b_idx*8 +: 8] <= {8{r_l1d_be[b_idx]}} & r_l1d_data[b_idx*8 +: 8] |
                                                    {8{r_stq_be[b_idx]}} & r_stq_data[b_idx*8 +: 8] ;
        snoop_if.resp_payload.be  [b_idx       ] <= r_l1d_be[b_idx] | r_stq_be[b_idx];
      end
    end else begin
      snoop_if.resp_valid <= 1'b0;
    end
  end
end

endmodule // msrh_snoop_top
