// `default_nettype none

module msrh_icache
  import msrh_lsu_pkg::*;
  import riscv_pkg::*;
(
  input logic                i_clk,
  input logic                i_reset_n,

  input logic                i_flush_valid,

  input                      ic_req_t i_s0_req,
  output logic               o_s0_ready,
  input logic [PADDR_W-1:0]  i_s1_paddr,
  input logic                i_s1_tlb_miss,

  output                     ic_resp_t o_s2_resp,

  output logic               o_s2_miss,
  output logic [VADDR_W-1:0] o_s2_miss_vaddr,

                             l2_req_if.master ic_l2_req,
                             l2_resp_if.slave ic_l2_resp
);

/* S1 stage */
logic                        r_s1_valid;
logic [ICACHE_WAY_W-1 : 0]   w_s1_tag_hit;
logic [VADDR_W-1:0]          r_s1_vaddr;
logic                        w_s1_hit;

/* S2 stage */
logic                        r_s2_valid;
logic                        r_s2_hit;
logic [ICACHE_WAY_W-1 : 0]   r_s2_tag_hit;
logic [msrh_conf_pkg::ICACHE_DATA_W-1: 0] w_s2_data[ICACHE_WAY_W];
logic [msrh_conf_pkg::ICACHE_DATA_W-1: 0] w_s2_selected_data;

logic [L2_CMD_TAG_W-1: 0]                 r_ic_req_tag;

typedef enum                              { ICInit, ICResp } ic_state_t;
ic_state_t r_ic_state;
logic                                     ic_l2_resp_fire;
logic [VADDR_W-1: 0]                      r_s2_vaddr;
logic [ICACHE_TAG_LOW-1: 0]               r_s2_waiting_vaddr;

generate for(genvar way = 0; way < ICACHE_WAY_W; way++) begin : icache_way_loop //
logic    w_s1_tag_valid;
logic [VADDR_W-1:ICACHE_TAG_LOW] w_s1_tag;

  tag_array
    #(
      .TAG_W(VADDR_W-ICACHE_TAG_LOW),
      .WORDS(ICACHE_TAG_LOW)
      )
  tag (
       .i_clk(i_clk),
       .i_reset_n(i_reset_n),

       .i_wr  (ic_l2_resp_fire),
       .i_addr(ic_l2_resp_fire ?
               r_s2_waiting_vaddr :
               i_s0_req.vaddr[$clog2(ICACHE_DATA_B_W) +: ICACHE_TAG_LOW]),
       .i_tag_valid  (1'b1),
       .i_tag (i_s0_req.vaddr[VADDR_W-1:ICACHE_TAG_LOW]),
       .o_tag(w_s1_tag),
       .o_tag_valid(w_s1_tag_valid)
       );

  assign w_s1_tag_hit[way] = (i_s1_paddr[VADDR_W-1:ICACHE_TAG_LOW] == w_s1_tag) & w_s1_tag_valid;

  data_array
    #(
      .WIDTH(msrh_conf_pkg::ICACHE_DATA_W),
      .ADDR_W(ICACHE_TAG_LOW)
      )
  data (
        .i_clk(i_clk),
        .i_reset_n(i_reset_n),
        .i_wr  (ic_l2_resp_fire),
        .i_addr(ic_l2_resp_fire ?
                r_s2_waiting_vaddr :
                r_s1_vaddr [$clog2(ICACHE_DATA_B_W) +: ICACHE_TAG_LOW]),
        .i_be  ({ICACHE_DATA_B_W{1'b1}}),
        .i_data(ic_l2_resp.payload.data),
        .o_data(w_s2_data[way])
        );

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_s2_tag_hit[way] <= 1'b0;
    end else begin
      r_s2_tag_hit[way] <= w_s1_tag_hit[way];
    end
  end

end
endgenerate

// ===============
// S1 stage
// ===============
assign w_s1_hit = (|w_s1_tag_hit) & !i_s1_tlb_miss;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s1_valid <= 1'b0;
    r_s1_vaddr <= {VADDR_W{1'b0}};
  end else begin
    // This valid is not flush:
    // Because this when flushed, same cycle new request is issued,
    // should'nt be flushed.
    r_s1_valid <= i_s0_req.valid & o_s0_ready;
    r_s1_vaddr <= i_s0_req.vaddr;
  end
end

// ===============
// S2 stage
// ===============
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_valid      <= 1'b0;
    r_s2_vaddr  <= 'h0;
  end else begin
    if (i_flush_valid) begin
      r_s2_valid <= 1'b0;
    end else begin
      r_s2_valid  <= r_s1_valid;
    end

    r_s2_hit    <= r_s1_valid & w_s1_hit;
    r_s2_vaddr  <= r_s1_vaddr;
  end
end



bit_oh_or
    #(
      .T(logic[msrh_conf_pkg::ICACHE_DATA_W-1:0]),
      .WORDS(ICACHE_WAY_W)
      )
cache_data_sel (
                .i_oh      (r_s2_tag_hit      ),
                .i_data    (w_s2_data         ),
                .o_selected(w_s2_selected_data)
                );

assign ic_l2_resp_fire = ic_l2_resp.valid & ic_l2_resp.ready &
                         (ic_l2_resp.payload.tag == {L2_UPPER_TAG_IC, {(L2_CMD_TAG_W-1){1'b0}}});
assign o_s2_resp.valid = !i_flush_valid & r_s2_valid & r_s2_hit & (r_ic_state == ICInit);
assign o_s2_resp.addr  = r_s2_vaddr [VADDR_W-1: 1];
assign o_s2_resp.data  = w_s2_selected_data;
assign o_s2_resp.be    = {ICACHE_DATA_B_W{1'b1}} &
                         ~((1 << r_s2_vaddr[$clog2(ICACHE_DATA_B_W)-1: 0])-1);
`ifdef SIMULATION
assign o_s2_resp.addr_dbg  = r_s2_vaddr [VADDR_W-1: 0];
`endif // SIMULATION

// ======================
// IC Miss State Machine
// ======================
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ic_state <= ICInit;
    ic_l2_req.valid <= 1'b0;
    ic_l2_req.payload <= 'h0;

    r_s2_waiting_vaddr <= 'h0;

    r_ic_req_tag <= 'h0;
  end else begin
    case (r_ic_state)
      ICInit : begin
        if (~i_flush_valid & r_s1_valid & !w_s1_hit) begin
          ic_l2_req.valid   <= 1'b1;
          ic_l2_req.payload.cmd  <= M_XRD;
          ic_l2_req.payload.addr <= i_s1_paddr;
          ic_l2_req.payload.tag  <= {L2_UPPER_TAG_IC, {(L2_CMD_TAG_W-1){1'b0}}};
          ic_l2_req.payload.data <= 'h0;
          ic_l2_req.payload.byte_en <= 'h0;
          if (ic_l2_req.ready) begin
            r_ic_state <= ICResp;
            r_s2_waiting_vaddr <= i_s1_paddr[$clog2(ICACHE_DATA_B_W) +: ICACHE_TAG_LOW];
          end
        end
      end
      ICResp : begin
        ic_l2_req.valid   <= 1'b0;
        if (ic_l2_resp_fire) begin
          r_ic_state <= ICInit;
          r_ic_req_tag <= r_ic_req_tag + 'h1;
        end
      end
    endcase // case (r_ic_state)
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign ic_l2_resp.ready = 1'b1;

assign o_s0_ready = (r_ic_state == ICInit);


// Missed Signal at s2
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    o_s2_miss <= 1'b0;
    o_s2_miss_vaddr <= 'h0;
  end else begin
    o_s2_miss       <= (r_ic_state == ICInit) & r_s1_valid & !i_flush_valid & !w_s1_hit;
    o_s2_miss_vaddr <= r_s1_vaddr;
  end
end

`ifdef SIMULATION
function void dump_json(int fp);
  $fwrite(fp, "  \"msrh_icache\" : {\n");

  if (i_s0_req.valid & o_s0_ready) begin
    $fwrite(fp, "    i_s0_req.valid : \"%d\",\n", i_s0_req.valid);
    $fwrite(fp, "    i_s0_req.vaddr : \"0x%x\",\n", i_s0_req.vaddr);
  end
  // $fwrite(fp, "    state : \"%d\",\n", r_ic_state);
  if (r_s1_valid) begin
    for(int way = 0; way < ICACHE_WAY_W; way++) begin
      $fwrite(fp, "    \"w_s1_tag_hit[%1d]\" : \"%d\",\n", way, w_s1_tag_hit[way]);
    end
  end
  if (r_s2_valid) begin
    $fwrite(fp, "    o_s2_miss : \"%d\",\n", o_s2_miss);
    $fwrite(fp, "    o_s2_miss_vaddr : \"0x%x\",\n", o_s2_miss_vaddr);
  end
  if (ic_l2_req.valid) begin
    $fwrite(fp, "    \"ic_l2_req\" : {\n");
    $fwrite(fp, "      valid : \"%d\",\n", ic_l2_req.valid);
    $fwrite(fp, "      cmd : \"%d\",\n", ic_l2_req.payload.cmd);
    $fwrite(fp, "      addr : \"0x%x\",\n", ic_l2_req.payload.addr);
    $fwrite(fp, "      tag : \"%d\",\n", ic_l2_req.payload.tag);
    $fwrite(fp, "    },\n");
  end

  if (o_s2_resp.valid) begin
    $fwrite(fp, "    \"o_s2_resp\" : {\n");
    $fwrite(fp, "      valid : \"%d\",\n", o_s2_resp.valid);
    $fwrite(fp, "      data : \"%x\",\n",  o_s2_resp.data);
    $fwrite(fp, "      miss : \"%d\",\n",  o_s2_miss);
    $fwrite(fp, "      vaddr : \"%d\",\n", o_s2_miss_vaddr);
    $fwrite(fp, "    },\n");
  end

  $fwrite(fp, "  },\n");
endfunction // dump
`endif // SIMULATION

endmodule

// `default_nettype wire
