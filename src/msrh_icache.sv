// `default_nettype none

module msrh_icache
  (
  input logic i_clk,
  input logic i_reset_n,

  input msrh_lsu_pkg::ic_req_t             i_s0_req,
  output logic                         o_s0_ready,
  input logic [riscv_pkg::PADDR_W-1:0] i_s1_paddr,
  input logic                          i_s1_tlb_miss,

  output msrh_lsu_pkg::ic_resp_t            o_s2_resp,

  output logic                          o_s2_miss,
  output logic [riscv_pkg::VADDR_W-1:0] o_s2_miss_vaddr,

  l2_req_if.master ic_l2_req,
  l2_resp_if.slave ic_l2_resp
);

    /* S1 stage */
    logic r_s1_valid;
    logic [msrh_lsu_pkg::ICACHE_WAY_W-1 : 0] w_s1_tag_hit;
    // logic [msrh_lsu_pkg::ICACHE_TAG_LOW-1:0] r_s1_addr_low_bit;
    logic [riscv_pkg::VADDR_W-1:0]       r_s1_vaddr;
    logic                                w_s1_hit;

    /* S2 stage */
    logic                               r_s2_valid;
    logic                               r_s2_hit;
    logic [msrh_lsu_pkg::ICACHE_WAY_W-1 : 0] r_s2_tag_hit;
    logic [msrh_lsu_pkg::ICACHE_DATA_W-1: 0] w_s2_data[msrh_lsu_pkg::ICACHE_WAY_W];
    logic [msrh_lsu_pkg::ICACHE_DATA_W-1: 0] w_s2_selected_data;

    logic [msrh_lsu_pkg::L2_CMD_TAG_W-1: 0]  r_ic_req_tag;

    typedef enum                        { ICInit, ICResp } ic_state_t;
    ic_state_t r_ic_state;
    logic                               ic_l2_resp_fire;
    logic [riscv_pkg::VADDR_W-1: 0]     r_req_vaddr;


    generate for(genvar way = 0; way < msrh_lsu_pkg::ICACHE_WAY_W; way++) begin : icache_way_loop //
        logic    w_s1_tag_valid;
        logic [riscv_pkg::VADDR_W-1:msrh_lsu_pkg::ICACHE_TAG_LOW] w_s1_tag;

        tag_array
            #(
              .TAG_W(riscv_pkg::VADDR_W-msrh_lsu_pkg::ICACHE_TAG_LOW),
              .WORDS(msrh_lsu_pkg::ICACHE_TAG_LOW)
              )
        tag (
             .i_clk(i_clk),
             .i_reset_n(i_reset_n),

             .i_wr  (ic_l2_resp_fire),
             .i_addr(ic_l2_resp_fire ?
                     r_req_vaddr   [$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W) +: msrh_lsu_pkg::ICACHE_TAG_LOW] :
                     i_s0_req.vaddr[$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W) +: msrh_lsu_pkg::ICACHE_TAG_LOW]),
             .i_tag_valid  (1'b1),
             .i_tag (i_s0_req.vaddr[riscv_pkg::VADDR_W-1:msrh_lsu_pkg::ICACHE_TAG_LOW]),
             .o_tag(w_s1_tag),
             .o_tag_valid(w_s1_tag_valid)
             );

        assign w_s1_tag_hit[way] = (i_s1_paddr[riscv_pkg::VADDR_W-1:msrh_lsu_pkg::ICACHE_TAG_LOW] == w_s1_tag) & w_s1_tag_valid;

        data_array
            #(
              .WIDTH(msrh_lsu_pkg::ICACHE_DATA_W),
              .ADDR_W(msrh_lsu_pkg::ICACHE_TAG_LOW)
              )
        data (
              .i_clk(i_clk),
              .i_reset_n(i_reset_n),
              .i_wr  (ic_l2_resp_fire),
              .i_addr(ic_l2_resp_fire ?
                      r_req_vaddr[$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W) +: msrh_lsu_pkg::ICACHE_TAG_LOW] :
                      r_s1_vaddr [$clog2(msrh_lsu_pkg::ICACHE_DATA_B_W) +: msrh_lsu_pkg::ICACHE_TAG_LOW]),
              .i_be  ({msrh_lsu_pkg::ICACHE_DATA_B_W{1'b1}}),
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
            r_s1_vaddr <= {riscv_pkg::VADDR_W{1'b0}};
        end else begin
            r_s1_valid <= i_s0_req.valid & o_s0_ready;
            r_s1_vaddr <= i_s0_req.vaddr;
        end
    end

    // ===============
    // S2 stage
    // ===============
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
        if (!i_reset_n) begin
            r_s2_valid <= 1'b0;
        end else begin
            r_s2_valid <= r_s1_valid;
            r_s2_hit   <= r_s1_valid & w_s1_hit;
        end
    end



    bit_oh_or
        #(
          .WIDTH(msrh_lsu_pkg::ICACHE_DATA_W),
          .WORDS(msrh_lsu_pkg::ICACHE_WAY_W)
          )
    cache_data_sel (
                    .i_oh      (r_s2_tag_hit      ),
                    .i_data    (w_s2_data         ),
                    .o_selected(w_s2_selected_data)
                    );

    assign ic_l2_resp_fire = ic_l2_resp.valid & ic_l2_resp.ready &
                             (ic_l2_resp.payload.tag == {msrh_lsu_pkg::L2_UPPER_TAG_IC, {(msrh_lsu_pkg::L2_CMD_TAG_W-1){1'b0}}});
    assign o_s2_resp.valid = r_s2_valid & r_s2_hit;
    assign o_s2_resp.addr  = r_req_vaddr [riscv_pkg::VADDR_W-1: 1];
    assign o_s2_resp.data  = w_s2_selected_data;
    assign o_s2_resp.be    = {msrh_lsu_pkg::ICACHE_DATA_B_W{1'b1}};

    // ======================
    // IC Miss State Machine
    // ======================
    always_ff @ (posedge i_clk, negedge i_reset_n) begin
        if (!i_reset_n) begin
            r_ic_state <= ICInit;
            ic_l2_req.valid <= 1'b0;
            ic_l2_req.payload <= 'h0;

            r_ic_req_tag <= 'h0;
          r_req_vaddr  <= 'h0;
        end else begin
            case (r_ic_state)
                ICInit : begin
                    if (r_s1_valid & !w_s1_hit) begin
                        ic_l2_req.valid   <= 1'b1;
                        ic_l2_req.payload.cmd  <= msrh_lsu_pkg::M_XRD;
                        ic_l2_req.payload.addr <= i_s1_paddr;
                        ic_l2_req.payload.tag  <= {msrh_lsu_pkg::L2_UPPER_TAG_IC, {(msrh_lsu_pkg::L2_CMD_TAG_W-1){1'b0}}};
                        ic_l2_req.payload.data <= 'h0;
                        ic_l2_req.payload.byte_en <= 'h0;
                        r_req_vaddr  <= r_s1_vaddr;
                        if (ic_l2_req.ready) begin
                            r_ic_state <= ICResp;
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
    o_s2_miss       <= (r_ic_state == ICInit) & r_s1_valid & !w_s1_hit;
    o_s2_miss_vaddr <= r_s1_vaddr;
  end
end

`ifdef SIMULATION
function void dump_json(int fp);
  $fwrite(fp, "  \"msrh_icache\" : {\n");

  if (i_s0_req.valid) begin
    $fwrite(fp, "    i_s0_req.valid : \"%d\",\n", i_s0_req.valid);
    $fwrite(fp, "    i_s0_req.vaddr : \"0x%x\",\n", i_s0_req.vaddr);
  end
  $fwrite(fp, "    state : \"%d\",\n", r_ic_state);
  for(int way = 0; way < msrh_lsu_pkg::ICACHE_WAY_W; way++) begin
    $fwrite(fp, "    w_s1_tag_hit[%d]: \"%d\",\n", way, w_s1_tag_hit[way]);
  end
  $fwrite(fp, "    o_s2_miss : \"%d\",\n", o_s2_miss);
  $fwrite(fp, "    o_s2_miss_vaddr : \"0x%x\",\n", o_s2_miss_vaddr);

  if (ic_l2_req.valid) begin
    $fwrite(fp, "    \"ic_l2_req\" : {\n");
    $fwrite(fp, "      valid : \"%d\",\n", ic_l2_req.valid);
    $fwrite(fp, "      cmd : \"%d\",\n", ic_l2_req.payload.cmd);
    $fwrite(fp, "      addr : \"0x%x\",\n", ic_l2_req.payload.addr);
    $fwrite(fp, "      tag : \"%d\",\n", ic_l2_req.payload.tag);
    $fwrite(fp, "    }\n");
  end

  $fwrite(fp, "  }\n");
endfunction // dump
`endif // SIMULATION

endmodule

// `default_nettype wire
