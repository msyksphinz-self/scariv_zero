// `default_nettype none

module msrh_icache
  import msrh_pkg::*;
  import msrh_ic_pkg::*;
  import msrh_lsu_pkg::*;
  import riscv_pkg::*;
(
  input logic      i_clk,
  input logic      i_reset_n,

  input logic      i_flush_valid,

  input logic      i_fence_i,

  input ic_req_t   i_s0_req,
  output logic     o_s0_ready,

  input paddr_t    i_s1_paddr,
  input logic      i_s1_kill,

  output ic_resp_t o_s2_resp,

 l2_req_if.master ic_l2_req,
 l2_resp_if.slave ic_l2_resp
);

/* S1 stage */
logic             r_s1_valid;
ic_ways_t         w_s1_tag_hit;
vaddr_t           r_s1_vaddr;
logic             w_s1_hit;

/* S2 stage */
logic             r_s2_valid;
logic             r_s2_hit;
ic_ways_t         r_s2_tag_hit;
paddr_t r_s2_paddr;
ic_data_t         w_s2_data[msrh_conf_pkg::ICACHE_WAYS];
ic_data_t         w_s2_selected_data;
logic             r_s2_normal_miss;


logic [L2_CMD_TAG_W-1: 0] r_ic_req_tag;

logic                     w_is_req_tag_normal_fetch;
logic                     w_is_req_tag_pre_fetch;
logic                     w_is_resp_tag_normal_fetch;
logic                     w_is_resp_tag_pre_fetch;

ic_state_t        r_ic_state;

logic                     ic_l2_normal_req_fire;
logic                     ic_l2_normal_resp_fire;
ic_ways_idx_t             r_s2_replace_way;
vaddr_t                   r_s2_vaddr;
vaddr_t                   r_s2_waiting_vaddr;

ic_ways_idx_t r_replace_way[2**ICACHE_TAG_LOW];
logic [ICACHE_TAG_LOW-1: 0] w_s2_replace_addr;
ic_ways_idx_t w_next_way;

logic [ICACHE_TAG_LOW-1: 0]                     w_tag_ram_addr;
logic [VADDR_W-1:ICACHE_TAG_LOW]                w_tag_ram_tag ;
logic [ICACHE_TAG_LOW-1: 0]                     w_dat_ram_addr;
ic_data_t                                       w_dat_ram_data;

// ------------------------
// Instruction Prefetcher
// ------------------------
logic   w_pref_l2_req_valid ;
paddr_t w_pref_l2_req_paddr ;
logic     w_s2_pref_paddr_hit;
ic_data_t w_s2_pref_hit_data;
logic     ic_l2_pref_req_fire;
logic     ic_l2_pref_resp_fire;

logic     w_pref_wr_valid;
logic     w_pref_wr_ready;
vaddr_t   w_pref_wr_vaddr;
ic_data_t w_pref_wr_data ;

logic     w_pref_wr_fire;
assign w_pref_wr_fire = w_pref_wr_valid & w_pref_wr_ready;

assign w_is_req_tag_normal_fetch = ic_l2_req.payload.tag == {L2_UPPER_TAG_IC, {(L2_CMD_TAG_W-2){1'b0}}};
assign w_is_req_tag_pre_fetch    = ic_l2_req.payload.tag == {L2_UPPER_TAG_IC, {(L2_CMD_TAG_W-3){1'b0}}, 1'b1};

assign w_is_resp_tag_normal_fetch = ic_l2_resp.payload.tag == {L2_UPPER_TAG_IC, {(L2_CMD_TAG_W-2){1'b0}}};
assign w_is_resp_tag_pre_fetch    = ic_l2_resp.payload.tag == {L2_UPPER_TAG_IC, {(L2_CMD_TAG_W-3){1'b0}}, 1'b1};

assign w_s2_replace_addr = r_s2_vaddr[$clog2(ICACHE_DATA_B_W) +: ICACHE_TAG_LOW];

generate if (msrh_conf_pkg::ICACHE_WAYS == 2) begin : replace_way_2
  assign w_next_way = ~r_replace_way[w_s2_replace_addr];
end else begin
  assign w_next_way = r_replace_way[w_s2_replace_addr] + 'h1;
end
endgenerate

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    for (int i = 0; i < 2**ICACHE_TAG_LOW; i++) begin
      r_replace_way[i] <= 'h0;
    end
  end else begin
    if (o_s2_resp.valid) begin
      r_replace_way[w_s2_replace_addr] <= w_next_way;
    end
  end
end // else: !if(msrh_conf_pkg::ICACHE_WAYS == 2)


assign w_tag_ram_addr = i_s0_req.valid         ? i_s0_req.vaddr    [$clog2(ICACHE_DATA_B_W) +: ICACHE_TAG_LOW] :
                        ic_l2_normal_resp_fire ? r_s2_waiting_vaddr[$clog2(ICACHE_DATA_B_W) +: ICACHE_TAG_LOW] :
                                                 w_pref_wr_vaddr   [$clog2(ICACHE_DATA_B_W) +: ICACHE_TAG_LOW];

assign w_tag_ram_tag = i_s0_req.valid         ? i_s0_req.vaddr    [VADDR_W-1:ICACHE_TAG_LOW] :
                       ic_l2_normal_resp_fire ? r_s2_waiting_vaddr[VADDR_W-1:ICACHE_TAG_LOW] :
                                                w_pref_wr_vaddr   [VADDR_W-1:ICACHE_TAG_LOW];

assign w_dat_ram_addr = r_s1_valid             ? r_s1_vaddr        [$clog2(ICACHE_DATA_B_W) +: ICACHE_TAG_LOW] :
                        ic_l2_normal_resp_fire ? r_s2_waiting_vaddr[$clog2(ICACHE_DATA_B_W) +: ICACHE_TAG_LOW] :
                                                 w_pref_wr_vaddr   [$clog2(ICACHE_DATA_B_W) +: ICACHE_TAG_LOW];

assign w_dat_ram_data = w_pref_wr_fire ? w_pref_wr_data :
                        ic_l2_resp.payload.data;

generate for(genvar way = 0; way < msrh_conf_pkg::ICACHE_WAYS; way++) begin : icache_way_loop //
  logic    w_s1_tag_valid;
  logic [VADDR_W-1:ICACHE_TAG_LOW] w_s1_tag;

  logic                    w_ram_wr;
  logic                    w_ram_rd;
  assign w_ram_wr = (r_replace_way[w_tag_ram_addr] == way) &
                    (ic_l2_normal_resp_fire | w_pref_wr_fire);
  assign w_ram_rd = i_s0_req.valid | ic_l2_normal_resp_fire;

  tag_array
    #(
      .TAG_W(VADDR_W-ICACHE_TAG_LOW),
      .WORDS(1 << ICACHE_TAG_LOW)
      )
  tag (
       .i_clk(i_clk),
       .i_reset_n(i_reset_n),

       .i_tag_clear(i_fence_i),

       .i_wr        (w_ram_wr       ),
       .i_addr      (w_tag_ram_addr ),
       .i_tag_valid (w_ram_rd       ),
       .i_tag       (w_tag_ram_tag  ),
       .o_tag       (w_s1_tag       ),
       .o_tag_valid (w_s1_tag_valid )
       );

  assign w_s1_tag_hit[way] = (r_s1_vaddr[VADDR_W-1:ICACHE_TAG_LOW] == w_s1_tag) & w_s1_tag_valid;

  data_array
    #(
      .WIDTH(msrh_conf_pkg::ICACHE_DATA_W),
      .WORDS(1 << ICACHE_TAG_LOW)
      )
  data (
        .i_clk(i_clk),
        .i_reset_n(i_reset_n),
        .i_wr  (w_ram_wr),
        .i_addr(w_dat_ram_addr),
        .i_be  ({ICACHE_DATA_B_W{1'b1}}),
        .i_data(w_dat_ram_data),
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
assign w_s1_hit = (|w_s1_tag_hit);

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
    .T(ic_data_t),
    .WORDS(msrh_conf_pkg::ICACHE_WAYS)
    )
cache_data_sel
  (
   .i_oh      (r_s2_tag_hit      ),
   .i_data    (w_s2_data         ),
   .o_selected(w_s2_selected_data)
   );

assign ic_l2_normal_req_fire  = ic_l2_req.valid  & ic_l2_req.ready  & w_is_req_tag_normal_fetch;
assign ic_l2_normal_resp_fire = ic_l2_resp.valid & ic_l2_resp.ready & w_is_resp_tag_normal_fetch;

assign o_s2_resp.valid = !i_flush_valid &
                         (w_s2_pref_paddr_hit |
                          r_s2_valid & r_s2_hit & (r_ic_state == ICInit));

assign o_s2_resp.vaddr = r_s2_vaddr [VADDR_W-1: 1];
assign o_s2_resp.data  = w_s2_pref_paddr_hit ? w_s2_pref_hit_data :
                         w_s2_selected_data;
assign o_s2_resp.be    = {ICACHE_DATA_B_W{1'b1}} &
                         ~((1 << r_s2_vaddr[$clog2(ICACHE_DATA_B_W)-1: 0])-1);
assign o_s2_resp.miss = r_s2_normal_miss & ~w_s2_pref_paddr_hit;

`ifdef SIMULATION
assign o_s2_resp.vaddr_dbg = r_s2_vaddr [VADDR_W-1: 0];
`endif // SIMULATION

// ======================
// IC Miss State Machine
// ======================
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_ic_state <= ICInit;

    r_s2_paddr <= 'h0;
    r_s2_waiting_vaddr <= 'h0;

    r_ic_req_tag <= 'h0;

  end else begin
    case (r_ic_state)
      ICInit : begin
        if (~i_flush_valid & r_s1_valid & !w_s1_hit & !i_s1_kill & !i_fence_i) begin
          r_ic_state <= ICCheckPref;
          r_s2_paddr <= i_s1_paddr;
          r_s2_replace_way <= r_replace_way[r_s1_vaddr[ICACHE_TAG_LOW-1: 0]];
          r_s2_waiting_vaddr <= r_s1_vaddr;
          // end
        end
      end // case: ICInit
      ICCheckPref : begin
        if (!w_s2_pref_paddr_hit) begin
          r_ic_state <= ICReq;
        end else begin
          r_ic_state <= ICInit;
        end
      end
      ICReq : begin
        if (ic_l2_req.ready & !i_fence_i) begin
          r_ic_state <= ICResp;
        end else if (i_fence_i) begin
          r_ic_state <= ICInvalidate;
        end
      end
      ICResp : begin
        if (ic_l2_normal_resp_fire) begin
          r_ic_state <= ICInit;
          r_ic_req_tag <= r_ic_req_tag + 'h1;
        end else if (i_fence_i) begin
          r_ic_state <= ICInvalidate;
        end
      end
      ICInvalidate: begin
        if (ic_l2_normal_resp_fire) begin
          r_ic_state <= ICInit;
          r_ic_req_tag <= r_ic_req_tag + 'h1;
        end
      end
      default : begin
      end
    endcase // case (r_ic_state)
  end
end // always_ff @ (posedge i_clk, negedge i_reset_n)

// --------------
// L2 Request
// --------------
always_comb begin
  if (w_pref_l2_req_valid) begin
    ic_l2_req.valid           = 1'b1;
    ic_l2_req.payload.cmd     = M_XRD;
    ic_l2_req.payload.addr    = w_pref_l2_req_paddr;
    ic_l2_req.payload.tag     = {L2_UPPER_TAG_IC, {(L2_CMD_TAG_W-3){1'b0}}, 1'b1};
    ic_l2_req.payload.data    = 'h0;
    ic_l2_req.payload.byte_en = 'h0;
  end else begin
    ic_l2_req.valid           = (r_ic_state == ICReq);
    ic_l2_req.payload.cmd     = M_XRD;
    ic_l2_req.payload.addr    = r_s2_paddr;
    ic_l2_req.payload.tag     = {L2_UPPER_TAG_IC, {(L2_CMD_TAG_W-2){1'b0}}};
    ic_l2_req.payload.data    = 'h0;
    ic_l2_req.payload.byte_en = 'h0;
  end // else: !if(w_pref_l2_req_valid)
end // always_comb

assign ic_l2_resp.ready = 1'b1;


assign o_s0_ready = (r_ic_state == ICInit);

// Missed Signal at s2
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_s2_normal_miss <= 1'b0;
  end else begin
    r_s2_normal_miss <= r_s1_valid &
                        ((r_ic_state == ICInit) & !i_flush_valid & !w_s1_hit |
                         (r_ic_state != ICInit));
  end
end


// =======================
// Instruction Prefetcher
// =======================
assign ic_l2_pref_req_fire  = ic_l2_req.valid  & ic_l2_req.ready  & w_is_req_tag_pre_fetch;
assign ic_l2_pref_resp_fire = ic_l2_resp.valid & ic_l2_resp.ready & w_is_resp_tag_pre_fetch;

assign w_pref_wr_ready = !(r_s1_valid | ic_l2_normal_resp_fire);

msrh_ic_pref
u_ic_pref
  (
   .i_clk     (i_clk),
   .i_reset_n (i_reset_n),

   .i_flush_valid (i_flush_valid),
   .i_fence_i     (i_fence_i),

   .i_ic_l2_req_fire  (ic_l2_normal_req_fire),
   .i_ic_l2_req_paddr (ic_l2_req.payload.addr),

   // Requests prefetch
   .o_pref_l2_req_valid (w_pref_l2_req_valid),
   .i_pref_l2_req_ready (ic_l2_req.ready),
   .o_pref_l2_req_paddr (w_pref_l2_req_paddr),

   // Response prefetech
   .i_pref_l2_resp_valid(ic_l2_pref_resp_fire),
   .i_pref_l2_resp_data (ic_l2_resp.payload.data),

   // Instruction Fetch search
   .i_s1_pref_search_valid (r_s1_valid          ),
   .i_s1_pref_search_vaddr (r_s1_vaddr          ),
   .i_s1_pref_search_paddr (i_s1_paddr          ),
   .o_s2_pref_search_hit   (w_s2_pref_paddr_hit ),
   .o_s2_pref_search_data  (w_s2_pref_hit_data  ),

   .o_ic_wr_valid ( w_pref_wr_valid ),
   .i_ic_wr_ready ( w_pref_wr_ready ),
   .o_ic_wr_vaddr ( w_pref_wr_vaddr ),
   .o_ic_wr_data  ( w_pref_wr_data  )
   );


`ifdef SIMULATION
function void dump_json(int fp);
  $fwrite(fp, "  \"msrh_icache\" : {\n");

  if (i_s0_req.valid & o_s0_ready) begin
    $fwrite(fp, "    i_s0_req.valid : \"%d\",\n", i_s0_req.valid);
    $fwrite(fp, "    i_s0_req.vaddr : \"0x%x\",\n", i_s0_req.vaddr);
  end
  // $fwrite(fp, "    state : \"%d\",\n", r_ic_state);
  if (r_s1_valid) begin
    for(int way = 0; way < msrh_conf_pkg::ICACHE_WAYS; way++) begin
      $fwrite(fp, "    \"w_s1_tag_hit[%1d]\" : \"%d\",\n", way, w_s1_tag_hit[way]);
    end
  end
  if (r_s2_valid) begin
    $fwrite(fp, "    o_s2_miss : \"%d\",\n", o_s2_resp.miss);
    $fwrite(fp, "    o_s2_miss_vaddr : \"0x%x\",\n", o_s2_resp.vaddr);
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
    $fwrite(fp, "      miss : \"%d\",\n",  o_s2_resp.miss);
    $fwrite(fp, "      vaddr : \"0x%x\",\n", o_s2_resp.vaddr);
    $fwrite(fp, "    },\n");
  end

  $fwrite(fp, "  },\n");
endfunction // dump

logic [63: 0] r_cycle_count;
logic [63: 0] r_s2_valid_count;
logic [63: 0] r_s2_miss_count;

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_cycle_count  <= 'h0;
    r_s2_valid_count <= 'h0;
    r_s2_miss_count    <= 'h0;
  end else begin
    r_cycle_count <= r_cycle_count + 'h1;
    if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
      r_s2_valid_count <= 'h0;
      r_s2_miss_count      <= 'h0;
    end else begin
      if (r_s2_valid) begin
        r_s2_valid_count <= r_s2_valid_count + 'h1;
        if (o_s2_resp.miss) begin
          r_s2_miss_count <= r_s2_miss_count + 'h1;
        end
      end
    end
  end
end

function void dump_perf (int fp);
  $fwrite(fp, "  \"icache\" : {");
  $fwrite(fp, "  \"request\" : %5d, ", r_s2_valid_count);
  $fwrite(fp, "  \"hit\" : %5d, ", r_s2_valid_count - r_s2_miss_count);
  $fwrite(fp, "  \"miss\" : %5d", r_s2_miss_count);
  $fwrite(fp, "  },\n");
endfunction // dump_perf

`endif // SIMULATION

endmodule

// `default_nettype wire
