// ------------------------------------------------------------------------
// NAME : scariv_vec_csu
// TYPE : module
// ------------------------------------------------------------------------
// Vector CSR Access Unit
// ------------------------------------------------------------------------
// vl / vtype / vlenb / vstart / vrm / vcsr / vxsat
// ------------------------------------------------------------------------

module scariv_vec_csr
  import scariv_pkg::*;
  import scariv_vec_pkg::*;
  (
   input logic i_clk,
   input logic i_reset_n,

   csr_rd_if.slave  read_csr_vec_if,
   csr_wr_if.slave  write_csr_vec_if,

   // Commit notification
   commit_if.monitor commit_if,

   output logic o_lmul_exception_mode
   );

riscv_pkg::xlen_t             r_vstart;
logic [$clog2(VLENBMAX)-1: 0] r_vl;
typedef struct packed {
  logic          vma;
  logic          vta;
  logic [ 2: 0]  vsew;
  logic [ 2: 0]  vlmul;
} vtype_t;
vtype_t          r_vtype;
logic            r_vill;
logic [$clog2(VLENBMAX)-1: 0] w_vlmax;

riscv_pkg::xlen_t r_vxrm;
riscv_pkg::xlen_t r_vcsr;
riscv_pkg::xlen_t r_vxsat;

logic [31: 0]                 r_vscratch; // keep for VLMUL change

logic                         r_lmul_exception_mode;

assign w_vlmax = (VLENB << r_vtype.vlmul) >> r_vtype.vsew;

always_comb begin
  read_csr_vec_if.resp_error = 1'b0;
  if (read_csr_vec_if.valid) begin
    case (read_csr_vec_if.addr)
      `SYSREG_ADDR_VSTART   : read_csr_vec_if.data = r_vstart;
      `SYSREG_ADDR_VXSAT    : read_csr_vec_if.data = r_vxsat;
      `SYSREG_ADDR_VXRM     : read_csr_vec_if.data = r_vxrm;
      `SYSREG_ADDR_VCSR     : read_csr_vec_if.data = r_vcsr;
      `SYSREG_ADDR_VL       : read_csr_vec_if.data = r_vl;
      `SYSREG_ADDR_VTYPE    : read_csr_vec_if.data = r_vtype;
      `SYSREG_ADDR_VSCRATCH : read_csr_vec_if.data = r_vscratch;
      `SYSREG_ADDR_VLENB    : read_csr_vec_if.data = VLENB;
      default : begin
        read_csr_vec_if.data = 'h0;
        read_csr_vec_if.resp_error = 1'b1;
      end
    endcase // case (read_csr_vec_if.addr)
  end else begin
    read_csr_vec_if.data = 'h0;
  end // if (read_csr_vec_if.valid)
end // always_comb


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
  end else begin
    if (write_csr_vec_if.valid) begin
      case (write_csr_vec_if.addr)
        `SYSREG_ADDR_VSTART   : r_vstart   <= write_csr_vec_if.data;
        `SYSREG_ADDR_VXSAT    : r_vxsat    <= write_csr_vec_if.data;
        `SYSREG_ADDR_VXRM     : r_vxrm     <= write_csr_vec_if.data;
        `SYSREG_ADDR_VCSR     : r_vcsr     <= write_csr_vec_if.data;
        `SYSREG_ADDR_VL       : r_vl       <= write_csr_vec_if.data;
        `SYSREG_ADDR_VTYPE    : r_vtype    <= write_csr_vec_if.data;
        `SYSREG_ADDR_VSCRATCH : r_vscratch <= write_csr_vec_if.data;
        default               : begin end
      endcase // case (write_csr_vec_if.addr)
    end // if (write_csr_vec_if.valid)
  end // else: !if(!i_reset_n)
end // always_ff @ (posedge i_clk, negedge i_reset_n)

assign write_csr_vec_if.resp_error = write_csr_vec_if.valid &
                                     (write_csr_vec_if.addr != `SYSREG_ADDR_VSTART)   &
                                     (write_csr_vec_if.addr != `SYSREG_ADDR_VXSAT)    &
                                     (write_csr_vec_if.addr != `SYSREG_ADDR_VXRM)     &
                                     (write_csr_vec_if.addr != `SYSREG_ADDR_VCSR)     &
                                     (write_csr_vec_if.addr != `SYSREG_ADDR_VL)       &
                                     (write_csr_vec_if.addr != `SYSREG_ADDR_VTYPE)    &
                                     (write_csr_vec_if.addr != `SYSREG_ADDR_VSCRATCH) &
                                     1'b0;

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_lmul_exception_mode <= 1'b0;
  end else begin
    if (commit_if.is_flushed_commit()) begin
      case (commit_if.payload.except_type)
        LMUL_CHANGE : begin
          r_lmul_exception_mode <= 1'b1;
          r_vscratch <= commit_if.payload.tval;
        end
        MRET,
        SRET,
        URET        : r_lmul_exception_mode <= 1'b0;
        default     : begin end
      endcase // case (commit_if.payload.except_type)
    end
  end
end

assign o_lmul_exception_mode = r_lmul_exception_mode;

endmodule // scariv_vec_csr
