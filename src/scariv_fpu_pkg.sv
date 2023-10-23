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
    Width:         64,
    EnableVectors: 1'b0,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b11000,
    IntFmtMask:    4'b0011
  };

  localparam fpnew_pkg::fpu_implementation_t SCARIV_FPNEW_IMPL = '{
    PipeRegs:   '{default: scariv_conf_pkg::FPNEW_LATENCY},
    UnitTypes:  '{'{default: fpnew_pkg::MERGED}, // ADDMUL
                  '{default: fpnew_pkg::MERGED}, // DIVSQRT
                  '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                  '{default: fpnew_pkg::MERGED}},  // CONV
    PipeConfig: fpnew_pkg::DISTRIBUTED
  };

endpackage // scariv_fpu_pkg
