module scariv_dcache
  import scariv_lsu_pkg::*;
#(
  parameter RD_PORT_NUM = scariv_conf_pkg::LSU_INST_NUM + 1 + 1 + 1
  )
(
   input logic i_clk,
   input logic i_reset_n,

   // LSU_INST_NUM ports from pipe, and STQ read and update port, PTW
   l1d_rd_if.slave l1d_rd_if[RD_PORT_NUM],
   l1d_wr_if.slave stbuf_l1d_wr_if,

   l1d_wr_if.slave stbuf_l1d_merge_if,
   l1d_wr_if.slave missu_l1d_wr_if,

   // MISSU search interface
   missu_dc_search_if.master missu_dc_search_if
   );

dc_read_resp_t[scariv_conf_pkg::DCACHE_BANKS-1: 0] w_dc_read_resp[RD_PORT_NUM];
dc_wr_req_t                                      w_s0_dc_wr_req;

logic [scariv_conf_pkg::DCACHE_BANKS-1: 0] r_dc_read_val[RD_PORT_NUM];

logic [scariv_conf_pkg::DCACHE_BANKS-1: 0] w_s0_wr_bank_valid;
logic [scariv_conf_pkg::DCACHE_BANKS-1: 0] r_s1_wr_bank_valid;
logic [scariv_conf_pkg::DCACHE_BANKS-1: 0] r_s2_wr_bank_valid;
dc_wr_resp_t [scariv_conf_pkg::DCACHE_BANKS-1: 0] w_s0_dc_wr_resp_bank;


generate for (genvar bank_idx = 0; bank_idx < scariv_conf_pkg::DCACHE_BANKS; bank_idx++) begin : bank_loop

  dc_read_req_t  w_dc_read_req [RD_PORT_NUM];
  dc_read_resp_t w_dc_read_resp_bank[RD_PORT_NUM];

  dc_wr_req_t  w_s0_dc_wr_req_bank;

  logic [$clog2(scariv_conf_pkg::DCACHE_BANKS)-1: 0] w_wr_paddr_bank;
  assign w_wr_paddr_bank = w_s0_dc_wr_req.s0_paddr[DCACHE_BANK_HIGH:DCACHE_BANK_LOW];
  assign w_s0_wr_bank_valid[bank_idx] = (w_wr_paddr_bank == bank_idx[$clog2(scariv_conf_pkg::DCACHE_BANKS)-1: 0]);

  always_comb begin
    w_s0_dc_wr_req_bank = w_s0_dc_wr_req;
    w_s0_dc_wr_req_bank.s0_valid = w_s0_dc_wr_req.s0_valid & w_s0_wr_bank_valid[bank_idx];
  end

  scariv_dcache_array
    #(.READ_PORT_NUM(RD_PORT_NUM))
  u_dcache_array
    (
     .i_clk     (i_clk    ),
     .i_reset_n (i_reset_n),

     .i_bank    (bank_idx[$clog2(scariv_conf_pkg::DCACHE_BANKS)-1: 0]),

     .i_dc_wr_req    (w_s0_dc_wr_req_bank ),
     .o_dc_wr_resp   (w_s0_dc_wr_resp_bank[bank_idx]),
     .i_dc_read_req  (w_dc_read_req        ),
     .o_dc_read_resp (w_dc_read_resp_bank  )
     );

  for (genvar p_idx = 0; p_idx < RD_PORT_NUM; p_idx++) begin : port_loop
    logic [$clog2(scariv_conf_pkg::DCACHE_BANKS)-1: 0] w_rd_paddr_bank;
    logic                                            w_rd_bank_valid;
    assign w_rd_paddr_bank = l1d_rd_if[p_idx].s0_paddr[DCACHE_BANK_HIGH:DCACHE_BANK_LOW];
    assign w_rd_bank_valid = (w_rd_paddr_bank == bank_idx[$clog2(scariv_conf_pkg::DCACHE_BANKS)-1: 0]);

    assign w_dc_read_req [p_idx].valid = l1d_rd_if[p_idx].s0_valid & w_rd_bank_valid;
    assign w_dc_read_req [p_idx].paddr = l1d_rd_if[p_idx].s0_paddr;
    assign w_dc_read_req [p_idx].lock_valid = l1d_rd_if[p_idx].s0_lock_valid;

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

  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_s1_wr_bank_valid[bank_idx] <= 1'b0;
      r_s2_wr_bank_valid[bank_idx] <= 1'b0;
    end else begin
      r_s1_wr_bank_valid[bank_idx] <= w_s0_wr_bank_valid[bank_idx];
      r_s2_wr_bank_valid[bank_idx] <= r_s1_wr_bank_valid[bank_idx];
    end
  end

end // block: bank_loop
endgenerate


generate for (genvar p_idx = 0; p_idx < RD_PORT_NUM; p_idx++) begin : rd_resp_loop
  dc_read_resp_t w_dc_read_resp_port;

  bit_oh_or_packed #(.T(dc_read_resp_t), .WORDS(scariv_conf_pkg::DCACHE_BANKS))
  resp_bit_or (.i_data(w_dc_read_resp[p_idx]), .i_oh(r_dc_read_val[p_idx]), .o_selected(w_dc_read_resp_port));

  assign l1d_rd_if[p_idx].s1_hit      = w_dc_read_resp_port.hit ;
  assign l1d_rd_if[p_idx].s1_hit_way  = w_dc_read_resp_port.hit_way ;
  assign l1d_rd_if[p_idx].s1_miss     = w_dc_read_resp_port.miss;
  assign l1d_rd_if[p_idx].s1_conflict = w_dc_read_resp_port.conflict;
  assign l1d_rd_if[p_idx].s1_data     = w_dc_read_resp_port.data;

end // block: rd_resp_loop
endgenerate


// ==========================
// L2 Reponse
// RESP1 : Getting Data
// ==========================
// logic r_rp1_l1d_exp_resp_valid;
// logic [scariv_pkg::MISSU_ENTRY_W-1:0] r_rp1_missu_resp_tag;
// logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0] r_rp1_missu_resp_data;
//
//
// // --------------------------------------------------
// // Interface of MISSU Search Entry to get information
// // --------------------------------------------------
// assign missu_dc_search_if.valid = r_rp1_l1d_exp_resp_valid;
// assign missu_dc_search_if.index = r_rp1_missu_resp_tag;
//
// // ===========================
// // L2 Reponse
// // RESP2 : Search MISSU Entiers
// // ===========================
//
// logic r_s0_valid;
// miss_entry_t r_s0_searched_missu_entry;
// logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0] r_s0_resp_data;
// logic [DCACHE_DATA_B_W-1: 0] r_s0_be;
// always_ff @ (posedge i_clk, negedge i_reset_n) begin
//   if (!i_reset_n) begin
//     r_s0_valid <= 1'b0;
//     r_s0_searched_missu_entry <= 'h0;
//     r_s0_resp_data <= 'h0;
//     r_s0_be <= 'h0;
//   end else begin
//     r_s0_valid <= r_rp1_l1d_exp_resp_valid;
//     r_s0_searched_missu_entry <= missu_dc_search_if.missu_entry;
//     r_s0_resp_data <= r_rp1_missu_resp_data;
//     r_s0_be        <= {DCACHE_DATA_B_W{1'b1}};
//   end
// end


// -------------
// Update of DC
// -------------
logic                                     w_s0_merge_valid;
logic [scariv_conf_pkg::DCACHE_DATA_W-1: 0] w_s0_merge_data;
scariv_lsu_pkg::mesi_t                      w_s0_merge_mesi;
assign w_s0_merge_valid = missu_l1d_wr_if.s0_valid | stbuf_l1d_merge_if.s0_valid;
generate for (genvar b_idx = 0; b_idx < DCACHE_DATA_B_W; b_idx++) begin : merge_byte_loop
  assign w_s0_merge_data[b_idx*8 +: 8] = stbuf_l1d_merge_if.s0_wr_req.s0_be[b_idx] ? stbuf_l1d_merge_if.s0_wr_req.s0_data[b_idx*8 +: 8] :
                                          missu_l1d_wr_if.s0_wr_req.s0_data[b_idx*8 +: 8];
end
endgenerate


dc_wr_resp_t w_s1_wr_selected_resp;
dc_wr_resp_t w_s2_wr_selected_resp;
bit_oh_or_packed #(.T(dc_wr_resp_t), .WORDS(scariv_conf_pkg::DCACHE_BANKS))
s1_resp_bit_or (.i_data(w_s0_dc_wr_resp_bank), .i_oh(r_s1_wr_bank_valid), .o_selected(w_s1_wr_selected_resp));
bit_oh_or_packed #(.T(dc_wr_resp_t), .WORDS(scariv_conf_pkg::DCACHE_BANKS))
s2_resp_bit_or (.i_data(w_s0_dc_wr_resp_bank), .i_oh(r_s2_wr_bank_valid), .o_selected(w_s2_wr_selected_resp));


assign w_s0_dc_wr_req.s0_valid            = w_s0_merge_valid | stbuf_l1d_wr_if.s0_valid;
assign w_s0_dc_wr_req.s0_tag_update_valid = w_s0_merge_valid;
assign w_s0_dc_wr_req.s0_paddr            = missu_l1d_wr_if.s0_valid ? missu_l1d_wr_if.s0_wr_req.s0_paddr :
                                            stbuf_l1d_wr_if.s0_wr_req.s0_paddr;
assign w_s0_dc_wr_req.s0_data             = missu_l1d_wr_if.s0_valid ? w_s0_merge_data :
                                            stbuf_l1d_wr_if.s0_wr_req.s0_data;
assign w_s0_dc_wr_req.s0_be               = missu_l1d_wr_if.s0_valid ? missu_l1d_wr_if.s0_wr_req.s0_be :
                                            stbuf_l1d_wr_if.s0_wr_req.s0_be;
assign w_s0_dc_wr_req.s0_mesi             = missu_l1d_wr_if.s0_valid ? missu_l1d_wr_if.s0_wr_req.s0_mesi :
                                            stbuf_l1d_wr_if.s0_wr_req.s0_mesi;
assign w_s0_dc_wr_req.s0_way              = missu_l1d_wr_if.s0_valid ? missu_l1d_wr_if.s0_wr_req.s0_way :
                                            stbuf_l1d_wr_if.s0_wr_req.s0_way;
logic w_s0_st_wr_confilct;
assign w_s0_st_wr_confilct = w_s0_merge_valid & stbuf_l1d_wr_if.s0_valid;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    stbuf_l1d_wr_if.s1_resp_valid          <= 1'b0;
    stbuf_l1d_wr_if.s1_wr_resp.s1_conflict <= 1'b0;
  end else begin
    stbuf_l1d_wr_if.s1_resp_valid          <= stbuf_l1d_wr_if.s0_valid;
    stbuf_l1d_wr_if.s1_wr_resp.s1_conflict <= w_s0_st_wr_confilct;
  end
end
assign stbuf_l1d_wr_if.s1_wr_resp.s1_hit  = w_s1_wr_selected_resp.s1_hit;
assign stbuf_l1d_wr_if.s1_wr_resp.s1_miss = w_s1_wr_selected_resp.s1_miss;
assign stbuf_l1d_wr_if.s2_done            = 1'b0;
assign stbuf_l1d_wr_if.s2_wr_resp.s2_evicted_valid = w_s2_wr_selected_resp.s2_evicted_valid;
assign stbuf_l1d_wr_if.s2_wr_resp.s2_evicted_data  = w_s2_wr_selected_resp.s2_evicted_data;
assign stbuf_l1d_wr_if.s2_wr_resp.s2_evicted_paddr = w_s2_wr_selected_resp.s2_evicted_paddr;


assign missu_l1d_wr_if.s1_wr_resp = stbuf_l1d_wr_if.s1_wr_resp;
assign missu_l1d_wr_if.s2_done    = stbuf_l1d_wr_if.s2_done;
assign missu_l1d_wr_if.s2_wr_resp = stbuf_l1d_wr_if.s2_wr_resp;

`ifdef SIMULATION
`ifdef VERILATOR
import "DPI-C" function void record_l1d_load
(
 input longint rtl_time,
 input longint paddr,
 input int     ram_addr,
 input byte    array[scariv_conf_pkg::DCACHE_DATA_W/8],
 input longint be, // Note: currently only support upto 512-bit (64-be).
 input int     merge_valid,
 input byte    merged_array[scariv_conf_pkg::DCACHE_DATA_W/8],
 input longint merge_be, // Note: currently only support upto 512-bit (64-be).
 input int     size
);

byte           l1d_array[scariv_conf_pkg::DCACHE_DATA_W/8];
byte           merged_l1d_array[scariv_conf_pkg::DCACHE_DATA_W/8];
generate for (genvar idx = 0; idx < scariv_conf_pkg::DCACHE_DATA_W/8; idx++) begin : array_loop
  assign l1d_array       [idx] = w_s0_dc_wr_req.s0_data[idx*8+:8];
  assign merged_l1d_array[idx] = w_s0_merge_data[idx*8+:8];
end
endgenerate

always_ff @ (negedge i_clk, negedge i_reset_n) begin
  if (i_reset_n) begin
    if (w_s0_dc_wr_req.s0_valid) begin
      /* verilator lint_off WIDTH */
      record_l1d_load($time,
                      w_s0_dc_wr_req.s0_paddr,
                      w_s0_dc_wr_req.s0_paddr[$clog2(DCACHE_DATA_B_W) +: DCACHE_TAG_LOW],
                      l1d_array,
                      w_s0_dc_wr_req.s0_be,
                      stbuf_l1d_merge_if.s0_valid,
                      merged_l1d_array,
                      stbuf_l1d_merge_if.s0_wr_req.s0_be,
                      DCACHE_DATA_B_W);
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


endmodule // scariv_dcache
