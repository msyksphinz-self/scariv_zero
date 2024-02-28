// ------------------------------------------------------------------------
// NAME : scariv_fpu_pkg
// TYPE : package
// ------------------------------------------------------------------------
// FPU Package
// ------------------------------------------------------------------------
// ------------------------------------------------------------------------

package scariv_fpu_pkg;

import decoder_fpu_ctrl_pkg::*;

  localparam fpnew_pkg::fpu_features_t SCARIV_FPNEW_FEATURE = '{
    Width:         unsigned'(riscv_fpu_pkg::FLEN_W),
    EnableVectors: 1'b0,
    EnableNanBox:  1'b1,
    FpFmtMask:     riscv_fpu_pkg::FLEN_W == 64 ? 5'b11000 : 5'b10000,  /* FLEN_W == 32 */
    IntFmtMask:    4'b0011
  };

  localparam fpnew_pkg::fpu_implementation_t SCARIV_FPNEW_IMPL = '{
    PipeRegs:   '{'{unsigned'(scariv_conf_pkg::FPNEW_LATENCY),
                    unsigned'(scariv_conf_pkg::FPNEW_LATENCY),
                    unsigned'(scariv_conf_pkg::FPNEW_LATENCY),
                    unsigned'(scariv_conf_pkg::FPNEW_LATENCY),
                    unsigned'(scariv_conf_pkg::FPNEW_LATENCY)},
                  '{default: unsigned'(scariv_conf_pkg::FPNEW_LATENCY-1)},
                  '{default: unsigned'(scariv_conf_pkg::FPNEW_LATENCY)},
                  '{default: unsigned'(scariv_conf_pkg::FPNEW_LATENCY)}},
    UnitTypes:  '{'{default: fpnew_pkg::MERGED}, // ADDMUL
                  '{default: fpnew_pkg::MERGED}, // DIVSQRT
                  '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                  '{default: fpnew_pkg::MERGED}},  // CONV
    PipeConfig: fpnew_pkg::DISTRIBUTED
  };

endpackage // scariv_fpu_pkg
