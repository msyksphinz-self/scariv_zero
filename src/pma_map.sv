module pma_map
  import msrh_lsu_pkg::*;
(
  input logic [riscv_pkg::PADDR_W-1: 0] i_pa,
  output logic o_map_hit,
  output map_attr_t o_map_attr
);


localparam MAP_TABLE_SIZE = 11;
logic [MAP_TABLE_SIZE-1: 0] w_hit_addr;
map_attr_t w_map_attr[MAP_TABLE_SIZE];
assign w_hit_addr[ 0] = (i_pa & 34'h000003fffff000) == 34'h00000000000000;  // Address Region : 0 - fff
assign w_map_attr[ 0].r = 1'b1;
assign w_map_attr[ 0].w = 1'b1;
assign w_map_attr[ 0].x = 1'b1;
assign w_map_attr[ 0].a = 1'b1;
assign w_map_attr[ 0].c = 1'b0;
assign w_hit_addr[ 1] = (i_pa & 34'h000003fffff000) == 34'h00000000002000;  // Address Region : 3000 - 3fff
assign w_map_attr[ 1].r = 1'b1;
assign w_map_attr[ 1].w = 1'b1;
assign w_map_attr[ 1].x = 1'b1;
assign w_map_attr[ 1].a = 1'b1;
assign w_map_attr[ 1].c = 1'b0;
assign w_hit_addr[ 2] = (i_pa & 34'h000003fffff000) == 34'h00000000004000;  // Address Region : 4000 - 4fff
assign w_map_attr[ 2].r = 1'b1;
assign w_map_attr[ 2].w = 1'b1;
assign w_map_attr[ 2].x = 1'b0;
assign w_map_attr[ 2].a = 1'b1;
assign w_map_attr[ 2].c = 1'b0;
assign w_hit_addr[ 3] = (i_pa & 34'h000003ffff0000) == 34'h00000000000000;  // Address Region : 10000 - 1ffff
assign w_map_attr[ 3].r = 1'b1;
assign w_map_attr[ 3].w = 1'b0;
assign w_map_attr[ 3].x = 1'b1;
assign w_map_attr[ 3].a = 1'b0;
assign w_map_attr[ 3].c = 1'b0;
assign w_hit_addr[ 4] = (i_pa & 34'h000003ffff0000) == 34'h00000000020000;  // Address Region : 20000 - 2ffff
assign w_map_attr[ 4].r = 1'b1;
assign w_map_attr[ 4].w = 1'b0;
assign w_map_attr[ 4].x = 1'b1;
assign w_map_attr[ 4].a = 1'b0;
assign w_map_attr[ 4].c = 1'b1;
assign w_hit_addr[ 5] = (i_pa & 34'h000003ffff0000) == 34'h00000002000000;  // Address Region : 2000000 - 200ffff
assign w_map_attr[ 5].r = 1'b1;
assign w_map_attr[ 5].w = 1'b1;
assign w_map_attr[ 5].x = 1'b0;
assign w_map_attr[ 5].a = 1'b1;
assign w_map_attr[ 5].c = 1'b1;
assign w_hit_addr[ 6] = (i_pa & 34'h000003fffff000) == 34'h00000002010000;  // Address Region : 2010000 - 2010fff
assign w_map_attr[ 6].r = 1'b1;
assign w_map_attr[ 6].w = 1'b1;
assign w_map_attr[ 6].x = 1'b0;
assign w_map_attr[ 6].a = 1'b1;
assign w_map_attr[ 6].c = 1'b0;
assign w_hit_addr[ 7] = (i_pa & 34'h000003fc000000) == 34'h00000008000000;  // Address Region : c000000 - fffffff
assign w_map_attr[ 7].r = 1'b1;
assign w_map_attr[ 7].w = 1'b1;
assign w_map_attr[ 7].x = 1'b0;
assign w_map_attr[ 7].a = 1'b1;
assign w_map_attr[ 7].c = 1'b0;
assign w_hit_addr[ 8] = (i_pa & 34'h000003fffff000) == 34'h00000010000000;  // Address Region : 10000000 - 10000fff
assign w_map_attr[ 8].r = 1'b1;
assign w_map_attr[ 8].w = 1'b1;
assign w_map_attr[ 8].x = 1'b1;
assign w_map_attr[ 8].a = 1'b1;
assign w_map_attr[ 8].c = 1'b1;
assign w_hit_addr[ 9] = (i_pa & 34'h000003fffff000) == 34'h00000054000000;  // Address Region : 54000000 - 54000fff
assign w_map_attr[ 9].r = 1'b1;
assign w_map_attr[ 9].w = 1'b1;
assign w_map_attr[ 9].x = 1'b0;
assign w_map_attr[ 9].a = 1'b1;
assign w_map_attr[ 9].c = 1'b0;
assign w_hit_addr[10] = (i_pa & 34'h000003f0000000) == 34'h00000080000000;  // Address Region : 80000000 - 8fffffff
assign w_map_attr[10].r = 1'b1;
assign w_map_attr[10].w = 1'b1;
assign w_map_attr[10].x = 1'b1;
assign w_map_attr[10].a = 1'b1;
assign w_map_attr[10].c = 1'b1;


assign o_map_hit = |w_hit_addr;
always_comb begin
case (w_hit_addr)
  11'b00000000001 : o_map_attr = w_map_attr[0];
  11'b00000000010 : o_map_attr = w_map_attr[1];
  11'b00000000100 : o_map_attr = w_map_attr[2];
  11'b00000001000 : o_map_attr = w_map_attr[3];
  11'b00000010000 : o_map_attr = w_map_attr[4];
  11'b00000100000 : o_map_attr = w_map_attr[5];
  11'b00001000000 : o_map_attr = w_map_attr[6];
  11'b00010000000 : o_map_attr = w_map_attr[7];
  11'b00100000000 : o_map_attr = w_map_attr[8];
  11'b01000000000 : o_map_attr = w_map_attr[9];
  11'b10000000000 : o_map_attr = w_map_attr[10];
  default   : o_map_attr = 'h0;
endcase
end

endmodule
