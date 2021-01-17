module tlb
 #(
    parameter USING_VM = 1'b1
 )
(
    input logic clk,
    input logic reset_n,

    input  mrh_pkg::tlb_req_t  i_tlb_req,
    output mrh_pkg::tlb_resp_t o_tlb_resp
);

  logic w_priv_s;
  logic w_priv_uses_vm;
  logic w_vpn [riscv_pkg::VADDR_W-1: riscv_pkg::PG_IDX_BITS];
  logic w_vm_enabled;
  logic [7: 0] w_hit_vector;
  mrh_pkg::tlb_entry_t entries[8];

  always_comb begin
    w_priv_s = priv[0];
    w_priv_uses_vm = priv <= riscv_pkg::PRIV_S;

    w_vm_enabled = USING_VM && ptw.ptbr.mode[ptw.ptbr.mode.getWidth-1] && w_priv_uses_vm;
  end

  generate for (genvar idx = 0; idx < 8; idx++) begin : entry_loop
    function logic tlb_hit(logic [riscv_pkg::VPN-1:0] vpn);
      if (superpage && usingVM) begin
        logic w_tag_match;
        w_tag_match = valid.head;
        for (int j=0; j<pgLevels; j++) begin
          logic base = vpnBits - (j + 1) * pgLevelBits;
          logic ignore = level < j || superpageOnly && j == pgLevels - 1;
          w_tag_match = w_tag_match && (ignore || tag(base + pgLevelBits - 1, base) === vpn(base + pgLevelBits - 1, base));
        end
        return w_tag_match;
      end else begin
        logic idx = sectorIdx(vpn)
        return valid(idx) && sectorw_tag_match(vpn);
      end
    endfunction

    assign w_hit_vector[idx] = w_vm_enabled & entries[idx];

  end
  endgenerate

endmodule

