module msrh_rename_map
  (
   input logic                              i_clk,
   input logic                              i_reset_n,

   input logic [msrh_conf_pkg::DISP_SIZE * 2-1:0] i_arch_valid,
   input logic [ 4: 0]                      i_arch_id[msrh_conf_pkg::DISP_SIZE * 2],
   output logic [msrh_pkg::RNID_W-1: 0]      o_rnid[msrh_conf_pkg::DISP_SIZE * 2],


   input logic [msrh_conf_pkg::DISP_SIZE-1:0]     i_update,
   input logic [ 4: 0]                      i_update_arch_id [msrh_conf_pkg::DISP_SIZE],
   input logic [msrh_pkg::RNID_W-1: 0]       i_update_rnid [msrh_conf_pkg::DISP_SIZE]
   );

logic [msrh_pkg::RNID_W-1: 0]                map[31: 0];

function logic [msrh_pkg::RNID_W: 0] select_latest_rnid (input logic [msrh_conf_pkg::DISP_SIZE-1:0] i_update,
                                                        input logic [ 4: 0]                tgt_arch_id,
                                                        input logic [ 4: 0]                i_update_arch_id [msrh_conf_pkg::DISP_SIZE],
                                                        input logic [msrh_pkg::RNID_W-1: 0] i_update_rnid [msrh_conf_pkg::DISP_SIZE]);
logic [msrh_pkg::RNID_W-1: 0]                                                               rnid_tmp[msrh_conf_pkg::DISP_SIZE];
logic [msrh_conf_pkg::DISP_SIZE-1: 0]                                                            valid_tmp;
logic [msrh_pkg::RNID_W: 0]                                                                 ret;

  for (int i = 0; i < msrh_conf_pkg::DISP_SIZE; i++) begin
    if (i_update[i] && i_update_arch_id[i] == tgt_arch_id) begin
      rnid_tmp [i] = i_update_rnid[i];
      valid_tmp[i] = 1'b1;
    end else begin
      if (i == 0) begin
        rnid_tmp [i] = 'h0;
        valid_tmp[i] = 1'b0;
      end else begin
        rnid_tmp [i] = rnid_tmp[i-1];
        valid_tmp[i] = valid_tmp[i-1];
      end
    end
  end

  ret = {valid_tmp[msrh_conf_pkg::DISP_SIZE-1], rnid_tmp[msrh_conf_pkg::DISP_SIZE-1]};
  return ret;

endfunction // select_latest_rnid


generate for (genvar i = 0; i < 32; i++) begin : map_loop
logic w_update;
logic [msrh_pkg::RNID_W-1: 0] w_update_rnid;
  assign {w_update, w_update_rnid} = select_latest_rnid (i_update,
                                                         i,
                                                         i_update_arch_id,
                                                         i_update_rnid);
  always_ff @ (posedge i_clk, negedge i_reset_n) begin
    if (!i_reset_n) begin
      map[i] <= i;
    end else begin
      if (w_update) begin
        map[i] <= w_update_rnid;
      end
    end
  end

end
endgenerate

generate for (genvar i = 0; i < msrh_conf_pkg::DISP_SIZE; i++) begin : rnid_loop
  assign o_rnid[i * 2 + 0] = map[i_arch_id[i * 2 + 0]];
  assign o_rnid[i * 2 + 1] = map[i_arch_id[i * 2 + 1]];
end
endgenerate


endmodule // msrh_rename_map
