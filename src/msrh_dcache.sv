module msrh_dcache
  import msrh_lsu_pkg::*;
#(
  parameter RD_PORT_NUM = msrh_conf_pkg::LSU_INST_NUM + 1 + 1 + 1
  )
(
   input logic i_clk,
   input logic i_reset_n,

   // LSU_INST_NUM ports from pipe, and STQ read and update port, PTW
   l1d_rd_if.slave l1d_rd_if[RD_PORT_NUM],
   l1d_wr_if.slave l1d_wr_if,
   l1d_wr_if.slave l1d_merge_if,

   // L2 cache response
   l2_resp_if.slave  l1d_ext_resp,

   // LRQ search interface
   lrq_search_if.master lrq_search_if
   );

dc_read_resp_t[msrh_conf_pkg::DCACHE_BANKS-1: 0] w_dc_read_resp[RD_PORT_NUM];
dc_update_t                                      w_rp2_dc_update;

logic [msrh_conf_pkg::DCACHE_BANKS-1: 0] r_dc_read_val[RD_PORT_NUM];

generate for (genvar bank_idx = 0; bank_idx < msrh_conf_pkg::DCACHE_BANKS; bank_idx++) begin : bank_loop

  l1d_rd_if l1d_rd_if_banks[RD_PORT_NUM]();

  dc_read_req_t  w_dc_read_req [RD_PORT_NUM];
  dc_read_resp_t w_dc_read_resp_bank[RD_PORT_NUM];

  dc_update_t w_rp2_dc_update_bank;

  logic [$clog2(msrh_conf_pkg::DCACHE_BANKS)-1: 0] w_wr_paddr_bank;
  logic                                            w_wr_bank_valid;
  assign w_wr_paddr_bank = w_rp2_dc_update.paddr[DCACHE_BANK_HIGH:DCACHE_BANK_LOW];
  assign w_wr_bank_valid = (w_wr_paddr_bank == bank_idx[$clog2(msrh_conf_pkg::DCACHE_BANKS)-1: 0]);

  always_comb begin
    w_rp2_dc_update_bank = w_rp2_dc_update;
    w_rp2_dc_update_bank.valid = w_rp2_dc_update.valid & w_wr_bank_valid;
  end

  msrh_dcache_array
    #(.READ_PORT_NUM(RD_PORT_NUM))
  u_dcache_array
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_dc_update    (w_rp2_dc_update_bank),
     .i_dc_read_req  (w_dc_read_req       ),
     .o_dc_read_resp (w_dc_read_resp_bank )
     );

  for (genvar p_idx = 0; p_idx < RD_PORT_NUM; p_idx++) begin : port_loop
    logic [$clog2(msrh_conf_pkg::DCACHE_BANKS)-1: 0] w_paddr_bank;
    logic                                            w_bank_valid;
    assign w_paddr_bank = l1d_rd_if[p_idx].s0_paddr[DCACHE_BANK_HIGH:DCACHE_BANK_LOW];
    assign w_bank_valid = (w_paddr_bank == bank_idx[$clog2(msrh_conf_pkg::DCACHE_BANKS)-1: 0]);

    assign w_dc_read_req [p_idx].valid = l1d_rd_if[p_idx].s0_valid & w_bank_valid;
    assign w_dc_read_req [p_idx].paddr = l1d_rd_if[p_idx].s0_paddr;
    assign w_dc_read_req [p_idx].h_pri = l1d_rd_if[p_idx].s0_h_pri;

    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_dc_read_val[p_idx][bank_idx] <= 1'b0;
      end else begin
        r_dc_read_val[p_idx][bank_idx] <= w_dc_read_req [p_idx].valid;
      end
    end

    // Reply distribution
    assign w_dc_read_resp[p_idx][bank_idx] = w_dc_read_resp_bank[p_idx];
  end

end // block: bank_loop
endgenerate


generate for (genvar p_idx = 0; p_idx < RD_PORT_NUM; p_idx++) begin : rd_resp_loop
  dc_read_resp_t w_dc_read_resp_port;

  bit_oh_or_packed #(.T(dc_read_resp_t), .WORDS(msrh_conf_pkg::DCACHE_BANKS))
  resp_bit_or (.i_data(w_dc_read_resp[p_idx]), .i_oh(r_dc_read_val[p_idx]), .o_selected(w_dc_read_resp_port));

  assign l1d_rd_if[p_idx].s1_hit      = w_dc_read_resp_port.hit ;
  assign l1d_rd_if[p_idx].s1_hit_way  = w_dc_read_resp_port.hit_way ;
  assign l1d_rd_if[p_idx].s1_miss     = w_dc_read_resp_port.miss;
  assign l1d_rd_if[p_idx].s1_conflict = w_dc_read_resp_port.conflict;
  assign l1d_rd_if[p_idx].s1_data     = w_dc_read_resp_port.data;

  assign l1d_rd_if[p_idx].s1_replace_valid = w_dc_read_resp_port.replace_valid;
  assign l1d_rd_if[p_idx].s1_replace_way   = w_dc_read_resp_port.replace_way;
  assign l1d_rd_if[p_idx].s1_replace_data  = w_dc_read_resp_port.replace_data;
  assign l1d_rd_if[p_idx].s1_replace_paddr = w_dc_read_resp_port.replace_paddr;

end // block: rd_resp_loop
endgenerate


// ==========================
// L2 Reponse
// RESP1 : Getting Data
// ==========================
logic r_rp1_l1d_exp_resp_valid;
logic [msrh_pkg::LRQ_ENTRY_W-1:0] r_rp1_lrq_resp_tag;
logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] r_rp1_lrq_resp_data;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_rp1_l1d_exp_resp_valid <= 1'b0;
    r_rp1_lrq_resp_tag <= 'h0;
    r_rp1_lrq_resp_data <= 'h0;
  end else begin
    r_rp1_l1d_exp_resp_valid <= l1d_ext_resp.valid &
                                (l1d_ext_resp.payload.tag[L2_CMD_TAG_W-1:L2_CMD_TAG_W-2] == L2_UPPER_TAG_RD_L1D);
    r_rp1_lrq_resp_tag       <= l1d_ext_resp.payload.tag[msrh_pkg::LRQ_ENTRY_W-1:0];
    r_rp1_lrq_resp_data      <= l1d_ext_resp.payload.data;
  end
end


// --------------------------------------------------
// Interface of LRQ Search Entry to get information
// --------------------------------------------------
assign lrq_search_if.valid = r_rp1_l1d_exp_resp_valid;
assign lrq_search_if.index = r_rp1_lrq_resp_tag;

// ===========================
// L2 Reponse
// RESP2 : Search LRQ Entiers
// ===========================

logic r_rp2_valid;
lrq_entry_t r_rp2_searched_lrq_entry;
logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] r_rp2_resp_data;
logic [DCACHE_DATA_B_W-1: 0] r_rp2_be;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_rp2_valid <= 1'b0;
    r_rp2_searched_lrq_entry <= 'h0;
    r_rp2_resp_data <= 'h0;
    r_rp2_be <= 'h0;
  end else begin
    r_rp2_valid <= r_rp1_l1d_exp_resp_valid;
    r_rp2_searched_lrq_entry <= lrq_search_if.lrq_entry;
    r_rp2_resp_data <= r_rp1_lrq_resp_data;
    r_rp2_be        <= {DCACHE_DATA_B_W{1'b1}};
  end
end


// -------------
// Update of DC
// -------------
logic                                     w_rp2_merge_valid;
logic [msrh_conf_pkg::DCACHE_DATA_W-1: 0] w_rp2_merge_data;
assign w_rp2_merge_valid = r_rp2_valid | l1d_merge_if.valid;
generate for (genvar b_idx = 0; b_idx < DCACHE_DATA_B_W; b_idx++) begin : merge_byte_loop
  assign w_rp2_merge_data[b_idx*8 +: 8] = l1d_merge_if.be[b_idx] ? l1d_merge_if.data[b_idx*8 +: 8] :
                                          r_rp2_resp_data[b_idx*8 +: 8];
end
endgenerate

assign w_rp2_dc_update.valid = w_rp2_merge_valid | l1d_wr_if.valid;
assign w_rp2_dc_update.paddr = r_rp2_valid ? r_rp2_searched_lrq_entry.paddr :
                               l1d_wr_if.paddr;
assign w_rp2_dc_update.data  = r_rp2_valid ? w_rp2_merge_data :
                               l1d_wr_if.data;
assign w_rp2_dc_update.be    = r_rp2_valid ? r_rp2_be :
                               l1d_wr_if.be;
assign w_rp2_dc_update.way   = r_rp2_valid ? r_rp2_searched_lrq_entry.evict.way :
                               l1d_wr_if.way;
assign l1d_wr_if.conflict = r_rp2_valid & l1d_wr_if.valid;


`ifdef SIMULATION
`ifdef VERILATOR
import "DPI-C" function void record_l1d_load
(
 input longint      rtl_time,
 input longint      paddr,
 input int          ram_addr,
 input int unsigned array[msrh_conf_pkg::DCACHE_DATA_W/32],
 input int          merge_valid,
 input int unsigned merged_array[msrh_conf_pkg::DCACHE_DATA_W/32],
 input int          size
);

int unsigned l1d_array[msrh_conf_pkg::DCACHE_DATA_W/32];
int unsigned merged_l1d_array[msrh_conf_pkg::DCACHE_DATA_W/32];
generate for (genvar idx = 0; idx < msrh_conf_pkg::DCACHE_DATA_W/32; idx++) begin : array_loop
  assign l1d_array[idx] = r_rp2_resp_data[idx*32+:32];
  assign merged_l1d_array[idx] = w_rp2_merge_data[idx*32+:32];
end
endgenerate

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (r_rp2_valid) begin
      /* verilator lint_off WIDTH */
      record_l1d_load($time,
                      r_rp2_searched_lrq_entry.paddr,
                      r_rp2_searched_lrq_entry.paddr[$clog2(DCACHE_DATA_B_W) +: DCACHE_TAG_LOW],
                      l1d_array,
                      l1d_merge_if.valid,
                      merged_l1d_array,
                      DCACHE_DATA_B_W);
      // $fwrite(msrh_pkg::STDERR, "%t : L1D Load-In   : %0x(%x) <= ",
      //         $time,
      //         r_rp2_searched_lrq_entry.paddr,
      //         r_rp2_searched_lrq_entry.paddr[$clog2(DCACHE_DATA_B_W) +: DCACHE_TAG_LOW]);
      // for (int i = DCACHE_DATA_B_W/4-1; i >=0 ; i--) begin
      //   $fwrite(msrh_pkg::STDERR, "%08x", r_rp2_resp_data[i*32 +: 32]);
      //   if (i != 0) begin
      //     $fwrite(msrh_pkg::STDERR, "_");
      //   end else begin
      //     $fwrite(msrh_pkg::STDERR, "\n");
      //   end
      // end
    end // if (l1d_wr_if.valid)
  end // if (i_reset_n)
end // always_ff @ (negedge i_clk, negedge i_reset_n)
`endif // VERILATOR


logic [63: 0] r_cycle_count;
logic [10: 0] r_req_valid_count [RD_PORT_NUM];
logic [10: 0] r_hit_count       [RD_PORT_NUM];
logic [10: 0] r_miss_count      [RD_PORT_NUM];
logic [10: 0] r_conflict_count  [RD_PORT_NUM];


always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_cycle_count  <= 'h0;
  end else begin
    r_cycle_count <= r_cycle_count + 'h1;
  end
end

generate for (genvar p_idx = 0; p_idx < RD_PORT_NUM; p_idx++) begin : perf_port_loop
  logic r_s1_valid;
  always_ff @ (negedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_req_valid_count [p_idx] <= 'h0;
      r_hit_count [p_idx] <= 'h0;
      r_miss_count [p_idx] <= 'h0;
      r_conflict_count [p_idx] <= 'h0;
    end else begin
      r_s1_valid <= l1d_rd_if[p_idx].s0_valid;
      if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
        r_req_valid_count [p_idx] <= 'h0;
        r_hit_count [p_idx] <= 'h0;
        r_miss_count [p_idx] <= 'h0;
        r_conflict_count [p_idx] <= 'h0;
      end else begin
        if (r_s1_valid) begin
          r_req_valid_count [p_idx] <= r_req_valid_count [p_idx] + 'h1;
          if (rd_resp_loop[p_idx].w_dc_read_resp_port.conflict) begin
            r_conflict_count [p_idx] <= r_conflict_count [p_idx] + 'h1;
          end else if (rd_resp_loop[p_idx].w_dc_read_resp_port.miss) begin
            r_miss_count [p_idx] <= r_miss_count [p_idx] + 'h1;
          end else if (rd_resp_loop[p_idx].w_dc_read_resp_port.hit) begin
            r_hit_count [p_idx] <= r_hit_count [p_idx] + 'h1;
          end
        end
      end // else: !if(r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
    end // else: !if(!i_reset_n)
  end // always_ff @ (negedge i_clk, negedge i_reset_n)
end // block: port_loop
endgenerate

function void dump_perf (int fp);

  $fwrite(fp, "  \"dcache\" : {\n");
  for (int p_idx = 0; p_idx < RD_PORT_NUM; p_idx++) begin : port_loop
    $fwrite(fp, "    \"port[%1d]\" : {", p_idx);
    $fwrite(fp, "    \"req\" : %5d, ", r_req_valid_count[p_idx]);
    $fwrite(fp, "    \"hit\" : %5d, ", r_hit_count[p_idx]);
    $fwrite(fp, "    \"miss\" : %5d, ", r_miss_count[p_idx]);
    $fwrite(fp, "    \"conflict\" : %5d", r_conflict_count[p_idx]);
    $fwrite(fp, "    \}\n");
  end
  $fwrite(fp, "  },\n");

endfunction // dump_perf

`endif // SIMULATION


endmodule // msrh_dcache
