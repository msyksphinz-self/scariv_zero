// ------------------------------------------------------------------------
// NAME : scariv_dcache
// TYPE : module
// ------------------------------------------------------------------------
// SCARIV Data Cache
// ------------------------------------------------------------------------
//
// ------------------------------------------------------------------------


module scariv_lsu_vipt_dcache
  import scariv_lsu_pkg::*;
(
   input logic i_clk,
   input logic i_reset_n,

   // LSU_INST_NUM ports from pipe, and
   l1d_rd_vipt_if.slave l1d_rd_vipt_if[scariv_conf_pkg::LSU_INST_NUM],
   // STQ read and update port, PTW
   l1d_rd_pipt_if.slave l1d_rd_pipt_if[scariv_lsu_pkg::L1D_PIPT_PORT_NUM],
   l1d_wr_if.slave stbuf_l1d_wr_if,

   l1d_wr_if.slave stbuf_l1d_merge_if,
   l1d_wr_if.slave missu_l1d_wr_if,

   l1d_wr_if.slave snoop_wr_if
   );

localparam RD_PORT_NUM = scariv_conf_pkg::LSU_INST_NUM +   // VIPT
                         L1D_PIPT_PORT_NUM;                // PIPT

dc_read_resp_t[scariv_conf_pkg::DCACHE_BANKS-1: 0] w_dc_read_resp[RD_PORT_NUM];
dc_wr_req_t                                        w_s0_dc_wr_req;

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

  scariv_lsu_vipt_dcache_array
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

  for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : port_vipt_loop
    logic [$clog2(scariv_conf_pkg::DCACHE_BANKS)-1: 0] w_rd_paddr_bank;
    logic                                            w_rd_bank_valid;
    assign w_rd_paddr_bank = l1d_rd_vipt_if[p_idx].s0_index[DCACHE_BANK_HIGH:DCACHE_BANK_LOW];
    assign w_rd_bank_valid = (w_rd_paddr_bank == bank_idx[$clog2(scariv_conf_pkg::DCACHE_BANKS)-1: 0]);

    assign w_dc_read_req [p_idx].valid         = l1d_rd_vipt_if[p_idx].s0_valid & w_rd_bank_valid;
    assign w_dc_read_req [p_idx].index         = l1d_rd_vipt_if[p_idx].s0_index;
    assign w_dc_read_req [p_idx].paddr_d1      = l1d_rd_vipt_if[p_idx].s1_paddr;
    assign w_dc_read_req [p_idx].high_priority = l1d_rd_vipt_if[p_idx].s0_high_priority;

    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_dc_read_val[p_idx][bank_idx] <= 1'b0;
      end else begin
        r_dc_read_val[p_idx][bank_idx] <= w_dc_read_req [p_idx].valid;
      end
    end

    // Reply distribution
    assign w_dc_read_resp[p_idx][bank_idx] = w_dc_read_resp_bank[p_idx];
  end // block: port_vipt_loop

  for (genvar p_idx = 0; p_idx < L1D_PIPT_PORT_NUM; p_idx++) begin : port_pipt_loop
    logic [$clog2(scariv_conf_pkg::DCACHE_BANKS)-1: 0] w_rd_paddr_bank;
    logic                                              w_rd_bank_valid;
    assign w_rd_paddr_bank = l1d_rd_pipt_if[p_idx].s0_paddr[DCACHE_BANK_HIGH:DCACHE_BANK_LOW];
    assign w_rd_bank_valid = (w_rd_paddr_bank == bank_idx[$clog2(scariv_conf_pkg::DCACHE_BANKS)-1: 0]);

    scariv_pkg::paddr_t r_paddr_d;
    always_ff @ (posedge i_clk) begin
      r_paddr_d <= l1d_rd_pipt_if[p_idx].s0_paddr;
    end

    assign w_dc_read_req [scariv_conf_pkg::LSU_INST_NUM + p_idx].valid         = l1d_rd_pipt_if[p_idx].s0_valid & w_rd_bank_valid;
    assign w_dc_read_req [scariv_conf_pkg::LSU_INST_NUM + p_idx].index         = gen_dc_pa_index(l1d_rd_pipt_if[p_idx].s0_paddr, l1d_rd_pipt_if[p_idx].s0_color);
    assign w_dc_read_req [scariv_conf_pkg::LSU_INST_NUM + p_idx].paddr_d1      = r_paddr_d;
    assign w_dc_read_req [scariv_conf_pkg::LSU_INST_NUM + p_idx].high_priority = l1d_rd_pipt_if[p_idx].s0_high_priority;

    always_ff @ (posedge i_clk, negedge i_reset_n) begin
      if (!i_reset_n) begin
        r_dc_read_val[scariv_conf_pkg::LSU_INST_NUM + p_idx][bank_idx] <= 1'b0;
      end else begin
        r_dc_read_val[scariv_conf_pkg::LSU_INST_NUM + p_idx][bank_idx] <= w_dc_read_req [scariv_conf_pkg::LSU_INST_NUM + p_idx].valid;
      end
    end

    // Reply distribution
    assign w_dc_read_resp[scariv_conf_pkg::LSU_INST_NUM + p_idx][bank_idx] = w_dc_read_resp_bank[scariv_conf_pkg::LSU_INST_NUM + p_idx];
  end // block: port_pipt_loop

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


generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : rd_vipt_resp_loop
  dc_read_resp_t w_dc_read_resp_port;

  bit_oh_or_packed #(.T(dc_read_resp_t), .WORDS(scariv_conf_pkg::DCACHE_BANKS))
  resp_bit_or (.i_data(w_dc_read_resp[p_idx]), .i_oh(r_dc_read_val[p_idx]), .o_selected(w_dc_read_resp_port));

  assign l1d_rd_vipt_if[p_idx].s1_hit      = w_dc_read_resp_port.hit ;
  assign l1d_rd_vipt_if[p_idx].s1_hit_way  = w_dc_read_resp_port.hit_way ;
  assign l1d_rd_vipt_if[p_idx].s1_miss     = w_dc_read_resp_port.miss;
  assign l1d_rd_vipt_if[p_idx].s1_conflict = w_dc_read_resp_port.conflict;
  assign l1d_rd_vipt_if[p_idx].s1_data     = w_dc_read_resp_port.data;

end endgenerate // block: rd_vipt_resp_loop


generate for (genvar p_idx = 0; p_idx < L1D_PIPT_PORT_NUM; p_idx++) begin : rd_pipt_resp_loop
  dc_read_resp_t w_dc_read_resp_port;

  bit_oh_or_packed #(.T(dc_read_resp_t), .WORDS(scariv_conf_pkg::DCACHE_BANKS))
  resp_bit_or (.i_data(w_dc_read_resp[scariv_conf_pkg::LSU_INST_NUM + p_idx]), .i_oh(r_dc_read_val[scariv_conf_pkg::LSU_INST_NUM + p_idx]), .o_selected(w_dc_read_resp_port));

  assign l1d_rd_pipt_if[p_idx].s1_hit      = w_dc_read_resp_port.hit ;
  assign l1d_rd_pipt_if[p_idx].s1_hit_way  = w_dc_read_resp_port.hit_way ;
  assign l1d_rd_pipt_if[p_idx].s1_miss     = w_dc_read_resp_port.miss;
  assign l1d_rd_pipt_if[p_idx].s1_conflict = w_dc_read_resp_port.conflict;
  assign l1d_rd_pipt_if[p_idx].s1_data     = w_dc_read_resp_port.data;

end endgenerate // block: rd_vipt_resp_loop



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


assign w_s0_dc_wr_req.s0_valid            = w_s0_merge_valid | stbuf_l1d_wr_if.s0_valid | snoop_wr_if.s0_valid;
assign w_s0_dc_wr_req.s0_tag_update_valid = w_s0_merge_valid | snoop_wr_if.s0_valid;
assign w_s0_dc_wr_req.s0_paddr            = snoop_wr_if.s0_valid     ? snoop_wr_if.s0_wr_req.s0_paddr     :
                                            missu_l1d_wr_if.s0_valid ? missu_l1d_wr_if.s0_wr_req.s0_paddr :
                                            stbuf_l1d_wr_if.s0_wr_req.s0_paddr;
assign w_s0_dc_wr_req.s0_color            = snoop_wr_if.s0_valid     ? snoop_wr_if.s0_wr_req.s0_color     :
                                            missu_l1d_wr_if.s0_valid ? missu_l1d_wr_if.s0_wr_req.s0_color :
                                            stbuf_l1d_wr_if.s0_wr_req.s0_color;
assign w_s0_dc_wr_req.s0_data             = snoop_wr_if.s0_valid     ? snoop_wr_if.s0_wr_req.s0_data     :
                                            missu_l1d_wr_if.s0_valid ? w_s0_merge_data :
                                            stbuf_l1d_wr_if.s0_wr_req.s0_data;
assign w_s0_dc_wr_req.s0_be               = snoop_wr_if.s0_valid     ? snoop_wr_if.s0_wr_req.s0_be     :
                                            missu_l1d_wr_if.s0_valid ? missu_l1d_wr_if.s0_wr_req.s0_be :
                                            stbuf_l1d_wr_if.s0_wr_req.s0_be;
assign w_s0_dc_wr_req.s0_mesi             = snoop_wr_if.s0_valid     ? snoop_wr_if.s0_wr_req.s0_mesi     :
                                            missu_l1d_wr_if.s0_valid ? missu_l1d_wr_if.s0_wr_req.s0_mesi :
                                            stbuf_l1d_wr_if.s0_wr_req.s0_mesi;
assign w_s0_dc_wr_req.s0_way              = snoop_wr_if.s0_valid     ? snoop_wr_if.s0_wr_req.s0_way     :
                                            missu_l1d_wr_if.s0_valid ? missu_l1d_wr_if.s0_wr_req.s0_way :
                                            stbuf_l1d_wr_if.s0_wr_req.s0_way;
logic w_s0_st_wr_conflict;
logic w_s0_missu_wr_conflict;
assign w_s0_st_wr_conflict    = (w_s0_merge_valid | snoop_wr_if.s0_valid) & stbuf_l1d_wr_if.s0_valid;
assign w_s0_missu_wr_conflict = (                   snoop_wr_if.s0_valid) & missu_l1d_wr_if.s0_valid;
always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    stbuf_l1d_wr_if.s1_resp_valid          <= 1'b0;
    stbuf_l1d_wr_if.s1_wr_resp.s1_conflict <= 1'b0;

    missu_l1d_wr_if.s1_resp_valid          <= 1'b0;
    missu_l1d_wr_if.s1_wr_resp.s1_conflict <= 1'b0;
  end else begin
    stbuf_l1d_wr_if.s1_resp_valid          <= stbuf_l1d_wr_if.s0_valid;
    stbuf_l1d_wr_if.s1_wr_resp.s1_conflict <= w_s0_st_wr_conflict;

    missu_l1d_wr_if.s1_resp_valid          <= missu_l1d_wr_if.s0_valid;
    missu_l1d_wr_if.s1_wr_resp.s1_conflict <= w_s0_missu_wr_conflict;
  end
end
assign stbuf_l1d_wr_if.s1_wr_resp.s1_hit  = w_s1_wr_selected_resp.s1_hit;
assign stbuf_l1d_wr_if.s1_wr_resp.s1_miss = w_s1_wr_selected_resp.s1_miss;
assign stbuf_l1d_wr_if.s2_done            = 1'b0;
assign stbuf_l1d_wr_if.s2_wr_resp.s2_evicted_valid = w_s2_wr_selected_resp.s2_evicted_valid;
assign stbuf_l1d_wr_if.s2_wr_resp.s2_evicted_data  = w_s2_wr_selected_resp.s2_evicted_data;
assign stbuf_l1d_wr_if.s2_wr_resp.s2_evicted_paddr = w_s2_wr_selected_resp.s2_evicted_paddr;
assign stbuf_l1d_wr_if.s2_wr_resp.s2_evicted_color = w_s2_wr_selected_resp.s2_evicted_color;
assign stbuf_l1d_wr_if.s2_wr_resp.s2_evicted_mesi  = w_s2_wr_selected_resp.s2_evicted_mesi;


assign missu_l1d_wr_if.s1_wr_resp.s1_hit  = w_s1_wr_selected_resp.s1_hit;
assign missu_l1d_wr_if.s1_wr_resp.s1_miss = w_s1_wr_selected_resp.s1_miss;
assign missu_l1d_wr_if.s2_done    = stbuf_l1d_wr_if.s2_done;
assign missu_l1d_wr_if.s2_wr_resp = stbuf_l1d_wr_if.s2_wr_resp;

`ifdef SIMULATION
  `ifdef COMPARE_ISS
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
  `endif // COMPARE_ISS


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

generate for (genvar p_idx = 0; p_idx < scariv_conf_pkg::LSU_INST_NUM; p_idx++) begin : perf_vipt_port_loop
  logic r_s1_valid;
  always_ff @ (negedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_req_valid_count [p_idx] <= 'h0;
      r_hit_count [p_idx] <= 'h0;
      r_miss_count [p_idx] <= 'h0;
      r_conflict_count [p_idx] <= 'h0;
    end else begin
      r_s1_valid <= l1d_rd_vipt_if[p_idx].s0_valid;
      if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
        r_req_valid_count [p_idx] <= 'h0;
        r_hit_count       [p_idx] <= 'h0;
        r_miss_count      [p_idx] <= 'h0;
        r_conflict_count  [p_idx] <= 'h0;
      end else begin
        if (r_s1_valid) begin
          r_req_valid_count [p_idx] <= r_req_valid_count [p_idx] + 'h1;
          if (rd_vipt_resp_loop[p_idx].w_dc_read_resp_port.conflict) begin
            r_conflict_count [p_idx] <= r_conflict_count [p_idx] + 'h1;
          end else if (rd_vipt_resp_loop[p_idx].w_dc_read_resp_port.miss) begin
            r_miss_count [p_idx] <= r_miss_count [p_idx] + 'h1;
          end else if (rd_vipt_resp_loop[p_idx].w_dc_read_resp_port.hit) begin
            r_hit_count [p_idx] <= r_hit_count [p_idx] + 'h1;
          end
        end
      end // else: !if(r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
    end // else: !if(!i_reset_n)
  end // always_ff @ (negedge i_clk, negedge i_reset_n)
end endgenerate


generate for (genvar p_idx = 0; p_idx < L1D_PIPT_PORT_NUM; p_idx++) begin : perf_pipt_port_loop
  logic r_s1_valid;
  always_ff @ (negedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      r_req_valid_count [p_idx] <= 'h0;
      r_hit_count [p_idx] <= 'h0;
      r_miss_count [p_idx] <= 'h0;
      r_conflict_count [p_idx] <= 'h0;
    end else begin
      r_s1_valid <= l1d_rd_pipt_if[p_idx].s0_valid;
      if (r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1) begin
        r_req_valid_count [p_idx] <= 'h0;
        r_hit_count       [p_idx] <= 'h0;
        r_miss_count      [p_idx] <= 'h0;
        r_conflict_count  [p_idx] <= 'h0;
      end else begin
        if (r_s1_valid) begin
          r_req_valid_count [p_idx] <= r_req_valid_count [p_idx] + 'h1;
          if (rd_pipt_resp_loop[p_idx].w_dc_read_resp_port.conflict) begin
            r_conflict_count [p_idx] <= r_conflict_count [p_idx] + 'h1;
          end else if (rd_pipt_resp_loop[p_idx].w_dc_read_resp_port.miss) begin
            r_miss_count [p_idx] <= r_miss_count [p_idx] + 'h1;
          end else if (rd_pipt_resp_loop[p_idx].w_dc_read_resp_port.hit) begin
            r_hit_count [p_idx] <= r_hit_count [p_idx] + 'h1;
          end
        end
      end // else: !if(r_cycle_count % sim_pkg::COUNT_UNIT == sim_pkg::COUNT_UNIT-1)
    end // else: !if(!i_reset_n)
  end // always_ff @ (negedge i_clk, negedge i_reset_n)
end endgenerate


integer total_valids[scariv_conf_pkg::DCACHE_BANKS][scariv_conf_pkg::DCACHE_WAYS];

generate for (genvar bank_idx = 0; bank_idx < scariv_conf_pkg::DCACHE_BANKS; bank_idx++) begin
  for (genvar way_idx = 0; way_idx < scariv_conf_pkg::DCACHE_WAYS; way_idx++) begin
    assign total_valids[bank_idx][way_idx] = $countones(bank_loop[bank_idx].u_dcache_array.dc_way_loop[way_idx].tag.r_tag_valids);
  end // else: !if(!i_reset_n)
end endgenerate

function automatic integer calc_valids();
  int ret = 0;
  for (int bank_idx = 0; bank_idx < scariv_conf_pkg::DCACHE_BANKS; bank_idx++) begin
    for (int way_idx = 0; way_idx < scariv_conf_pkg::DCACHE_WAYS; way_idx++) begin
      ret = ret + total_valids[bank_idx][way_idx];
    end
  end
  return ret;

endfunction // calc_valids


function void dump_perf (int fp);

  $fwrite(fp, "  \"dcache\" : {\n");
  $fwrite(fp, "    \"filled : %d, words : %d, size : %dKB},\n", calc_valids(),
          scariv_conf_pkg::DCACHE_WORDS * scariv_conf_pkg::DCACHE_WAYS,
          (scariv_conf_pkg::DCACHE_WORDS * scariv_conf_pkg::DCACHE_WAYS * scariv_conf_pkg::ICACHE_DATA_W) / 8 / 1024 );
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


endmodule // scariv_lsu_vipt_dcache
