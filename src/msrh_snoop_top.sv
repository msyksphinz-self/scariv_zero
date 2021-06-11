module msrh_snoop_top
  import msrh_lsu_pkg::*;
  (
    input logic i_clk,
    input logic i_reset_n,

    // Cache Coherent Interface
    snoop_if.slave snoop_if,

    // Internal Broadcast Interface
    snoop_bcast_if.master snoop_bcast_if
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

state_t                r_state;
logic [MAX_INDEX-1: 0] r_resp_valid;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    snoop_bcast_if.req_valid <= 1'b0;
  end else begin
    snoop_bcast_if.req_valid   <= snoop_if.req_valid;
    snoop_bcast_if.req_payload <= snoop_if.req_payload;
    case (r_state)
      IDLE      : begin
        if (snoop_if.req_valid) begin
          r_state <= WAIT_RESP;
        end
      end
      WAIT_RESP : begin
        if (&r_resp_valid) begin
          r_state <= IDLE;
        end
      end
      default : begin
        $fatal(0, "default state reached.");
      end
    endcase // case (r_state)
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_resp_valid <= 'h0;
  end else begin
    case (r_state)
      IDLE : r_resp_valid <= 'h0;
      WAIT_RESP : begin
        if (snoop_bcast_if.resp_l1d_valid) begin
          r_resp_valid[L1D_INDEX] <= 1'b1;
        end
        if (snoop_bcast_if.resp_stq_valid) begin
          r_resp_valid[STQ_INDEX] <= 1'b1;
        end
      end
      default : begin
        $fatal(0, "default state reached.");
      end
    endcase // case (r_state)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)


endmodule // msrh_snoop_top
