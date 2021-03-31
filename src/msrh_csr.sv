module msrh_csr
  import riscv_pkg::*;
  (
   input logic                i_clk,
   input logic                i_reset_n,

   input logic                i_rd_vld,
   input logic [11: 0]        i_rd_addr,
   output logic [XLEN_W-1: 0] o_rd_data,

   input logic                i_wr_vld,
   input logic [11: 0]        i_wr_addr,
   input logic [XLEN_W-1: 0]  i_wr_data,

   output logic               o_xcpt
   );

`include "msrh_csr_def.svh"

logic [XLEN_W-1: 0] r_ustatus;
logic [XLEN_W-1: 0] r_uie;
logic [XLEN_W-1: 0] r_utvec;
logic [XLEN_W-1: 0] r_vstart;
logic [XLEN_W-1: 0] r_vxsat;
logic [XLEN_W-1: 0] r_vxrm;
logic [XLEN_W-1: 0] r_uscratch;
logic [XLEN_W-1: 0] r_uepc;
logic [XLEN_W-1: 0] r_ucause;
logic [XLEN_W-1: 0] r_ubadaddr;
logic [XLEN_W-1: 0] r_uip;
logic [XLEN_W-1: 0] r_fflags;
logic [XLEN_W-1: 0] r_frm;
logic [XLEN_W-1: 0] r_fcsr;
logic [XLEN_W-1: 0] r_cycle;
logic [XLEN_W-1: 0] r_instret;
logic [XLEN_W-1: 0] r_hpmcounter3;
logic [XLEN_W-1: 0] r_hpmcounter4;
logic [XLEN_W-1: 0] r_hpmcounter5;
logic [XLEN_W-1: 0] r_hpmcounter6;
logic [XLEN_W-1: 0] r_hpmcounter7;
logic [XLEN_W-1: 0] r_hpmcounter8;
logic [XLEN_W-1: 0] r_hpmcounter9;
logic [XLEN_W-1: 0] r_hpmcounter10;
logic [XLEN_W-1: 0] r_hpmcounter11;
logic [XLEN_W-1: 0] r_hpmcounter12;
logic [XLEN_W-1: 0] r_hpmcounter13;
logic [XLEN_W-1: 0] r_hpmcounter14;
logic [XLEN_W-1: 0] r_hpmcounter15;
logic [XLEN_W-1: 0] r_hpmcounter16;
logic [XLEN_W-1: 0] r_hpmcounter17;
logic [XLEN_W-1: 0] r_hpmcounter18;
logic [XLEN_W-1: 0] r_hpmcounter19;
logic [XLEN_W-1: 0] r_hpmcounter20;
logic [XLEN_W-1: 0] r_hpmcounter21;
logic [XLEN_W-1: 0] r_hpmcounter22;
logic [XLEN_W-1: 0] r_hpmcounter23;
logic [XLEN_W-1: 0] r_hpmcounter24;
logic [XLEN_W-1: 0] r_hpmcounter25;
logic [XLEN_W-1: 0] r_hpmcounter26;
logic [XLEN_W-1: 0] r_hpmcounter27;
logic [XLEN_W-1: 0] r_hpmcounter28;
logic [XLEN_W-1: 0] r_hpmcounter29;
logic [XLEN_W-1: 0] r_hpmcounter30;
logic [XLEN_W-1: 0] r_hpmcounter31;
logic [XLEN_W-1: 0] r_cycleh;
logic [XLEN_W-1: 0] r_timeh;
logic [XLEN_W-1: 0] r_instreth;
logic [XLEN_W-1: 0] r_hpmcounterh3;
logic [XLEN_W-1: 0] r_hpmcounterh4;
logic [XLEN_W-1: 0] r_hpmcounterh5;
logic [XLEN_W-1: 0] r_hpmcounterh6;
logic [XLEN_W-1: 0] r_hpmcounterh7;
logic [XLEN_W-1: 0] r_hpmcounterh8;
logic [XLEN_W-1: 0] r_hpmcounterh9;
logic [XLEN_W-1: 0] r_hpmcounterh10;
logic [XLEN_W-1: 0] r_hpmcounterh11;
logic [XLEN_W-1: 0] r_hpmcounterh12;
logic [XLEN_W-1: 0] r_hpmcounterh13;
logic [XLEN_W-1: 0] r_hpmcounterh14;
logic [XLEN_W-1: 0] r_hpmcounterh15;
logic [XLEN_W-1: 0] r_hpmcounterh16;
logic [XLEN_W-1: 0] r_hpmcounterh17;
logic [XLEN_W-1: 0] r_hpmcounterh18;
logic [XLEN_W-1: 0] r_hpmcounterh19;
logic [XLEN_W-1: 0] r_hpmcounterh20;
logic [XLEN_W-1: 0] r_hpmcounterh21;
logic [XLEN_W-1: 0] r_hpmcounterh22;
logic [XLEN_W-1: 0] r_hpmcounterh23;
logic [XLEN_W-1: 0] r_hpmcounterh24;
logic [XLEN_W-1: 0] r_hpmcounterh25;
logic [XLEN_W-1: 0] r_hpmcounterh26;
logic [XLEN_W-1: 0] r_hpmcounterh27;
logic [XLEN_W-1: 0] r_hpmcounterh28;
logic [XLEN_W-1: 0] r_hpmcounterh29;
logic [XLEN_W-1: 0] r_hpmcounterh30;
logic [XLEN_W-1: 0] r_hpmcounterh31;
logic [XLEN_W-1: 0] r_sstatus;
logic [XLEN_W-1: 0] r_sedeleg;
logic [XLEN_W-1: 0] r_sideleg;
logic [XLEN_W-1: 0] r_sie;
logic [XLEN_W-1: 0] r_stvec;
logic [XLEN_W-1: 0] r_scounteren;
logic [XLEN_W-1: 0] r_sscratch;
logic [XLEN_W-1: 0] r_sepc;
logic [XLEN_W-1: 0] r_scause;
logic [XLEN_W-1: 0] r_stval;
logic [XLEN_W-1: 0] r_sip;
logic [XLEN_W-1: 0] r_satp;
logic [XLEN_W-1: 0] r_hstatus;
logic [XLEN_W-1: 0] r_hedeleg;
logic [XLEN_W-1: 0] r_hideleg;
logic [XLEN_W-1: 0] r_hie;
logic [XLEN_W-1: 0] r_htvec;
logic [XLEN_W-1: 0] r_hscratch;
logic [XLEN_W-1: 0] r_hepc;
logic [XLEN_W-1: 0] r_hcause;
logic [XLEN_W-1: 0] r_hbadaddr;
logic [XLEN_W-1: 0] r_hip;
logic [XLEN_W-1: 0] r_hptbr;
logic [XLEN_W-1: 0] r_mvendorid;
logic [XLEN_W-1: 0] r_marchid;
logic [XLEN_W-1: 0] r_mimpid;
logic [XLEN_W-1: 0] r_mhartid;
logic [XLEN_W-1: 0] r_mstatus;
logic [XLEN_W-1: 0] r_misa;
logic [XLEN_W-1: 0] r_medeleg;
logic [XLEN_W-1: 0] r_mideleg;
logic [XLEN_W-1: 0] r_mie;
logic [XLEN_W-1: 0] r_mtvec;
logic [XLEN_W-1: 0] r_mcounteren;
logic [XLEN_W-1: 0] r_mscratch;
logic [XLEN_W-1: 0] r_mepc;
logic [XLEN_W-1: 0] r_mcause;
logic [XLEN_W-1: 0] r_mtval;
logic [XLEN_W-1: 0] r_mip;
logic [XLEN_W-1: 0] r_mbase;
logic [XLEN_W-1: 0] r_mbound;
logic [XLEN_W-1: 0] r_mibase;
logic [XLEN_W-1: 0] r_mibound;
logic [XLEN_W-1: 0] r_mdbase;
logic [XLEN_W-1: 0] r_mdbound;
logic [XLEN_W-1: 0] r_mcycle;
logic [XLEN_W-1: 0] r_minstret;
logic [XLEN_W-1: 0] r_mhpmcounter3;
logic [XLEN_W-1: 0] r_mhpmcounter4;
logic [XLEN_W-1: 0] r_mhpmcounter5;
logic [XLEN_W-1: 0] r_mhpmcounter6;
logic [XLEN_W-1: 0] r_mhpmcounter7;
logic [XLEN_W-1: 0] r_mhpmcounter8;
logic [XLEN_W-1: 0] r_mhpmcounter9;
logic [XLEN_W-1: 0] r_mhpmcounter10;
logic [XLEN_W-1: 0] r_mhpmcounter11;
logic [XLEN_W-1: 0] r_mhpmcounter12;
logic [XLEN_W-1: 0] r_mhpmcounter13;
logic [XLEN_W-1: 0] r_mhpmcounter14;
logic [XLEN_W-1: 0] r_mhpmcounter15;
logic [XLEN_W-1: 0] r_mhpmcounter16;
logic [XLEN_W-1: 0] r_mhpmcounter17;
logic [XLEN_W-1: 0] r_mhpmcounter18;
logic [XLEN_W-1: 0] r_mhpmcounter19;
logic [XLEN_W-1: 0] r_mhpmcounter20;
logic [XLEN_W-1: 0] r_mhpmcounter21;
logic [XLEN_W-1: 0] r_mhpmcounter22;
logic [XLEN_W-1: 0] r_mhpmcounter23;
logic [XLEN_W-1: 0] r_mhpmcounter24;
logic [XLEN_W-1: 0] r_mhpmcounter25;
logic [XLEN_W-1: 0] r_mhpmcounter26;
logic [XLEN_W-1: 0] r_mhpmcounter27;
logic [XLEN_W-1: 0] r_mhpmcounter28;
logic [XLEN_W-1: 0] r_mhpmcounter29;
logic [XLEN_W-1: 0] r_mhpmcounter30;
logic [XLEN_W-1: 0] r_mhpmcounter31;
logic [XLEN_W-1: 0] r_mhpevent3;
logic [XLEN_W-1: 0] r_mhpevent4;
logic [XLEN_W-1: 0] r_mhpevent5;
logic [XLEN_W-1: 0] r_mhpevent6;
logic [XLEN_W-1: 0] r_mhpevent7;
logic [XLEN_W-1: 0] r_mhpevent8;
logic [XLEN_W-1: 0] r_mhpevent9;
logic [XLEN_W-1: 0] r_mhpevent10;
logic [XLEN_W-1: 0] r_mhpevent11;
logic [XLEN_W-1: 0] r_mhpevent12;
logic [XLEN_W-1: 0] r_mhpevent13;
logic [XLEN_W-1: 0] r_mhpevent14;
logic [XLEN_W-1: 0] r_mhpevent15;
logic [XLEN_W-1: 0] r_mhpevent16;
logic [XLEN_W-1: 0] r_mhpevent17;
logic [XLEN_W-1: 0] r_mhpevent18;
logic [XLEN_W-1: 0] r_mhpevent19;
logic [XLEN_W-1: 0] r_mhpevent20;
logic [XLEN_W-1: 0] r_mhpevent21;
logic [XLEN_W-1: 0] r_mhpevent22;
logic [XLEN_W-1: 0] r_mhpevent23;
logic [XLEN_W-1: 0] r_mhpevent24;
logic [XLEN_W-1: 0] r_mhpevent25;
logic [XLEN_W-1: 0] r_mhpevent26;
logic [XLEN_W-1: 0] r_mhpevent27;
logic [XLEN_W-1: 0] r_mhpevent28;
logic [XLEN_W-1: 0] r_mhpevent29;
logic [XLEN_W-1: 0] r_mhpevent30;
logic [XLEN_W-1: 0] r_mhpevent31;
logic [XLEN_W-1: 0] r_pmpcfg0;
logic [XLEN_W-1: 0] r_pmpcfg1;
logic [XLEN_W-1: 0] r_pmpcfg2;
logic [XLEN_W-1: 0] r_pmpcfg3;
logic [XLEN_W-1: 0] r_pmpaddr0;
logic [XLEN_W-1: 0] r_pmpaddr1;
logic [XLEN_W-1: 0] r_pmpaddr2;
logic [XLEN_W-1: 0] r_pmpaddr3;
logic [XLEN_W-1: 0] r_pmpaddr4;
logic [XLEN_W-1: 0] r_pmpaddr5;
logic [XLEN_W-1: 0] r_pmpaddr6;
logic [XLEN_W-1: 0] r_pmpaddr7;
logic [XLEN_W-1: 0] r_pmpaddr8;
logic [XLEN_W-1: 0] r_pmpaddr9;
logic [XLEN_W-1: 0] r_pmpaddr10;
logic [XLEN_W-1: 0] r_pmpaddr11;
logic [XLEN_W-1: 0] r_pmpaddr12;
logic [XLEN_W-1: 0] r_pmpaddr13;
logic [XLEN_W-1: 0] r_pmpaddr14;
logic [XLEN_W-1: 0] r_pmpaddr15;
logic [XLEN_W-1: 0] r_stats;

always_comb begin
  o_xcpt = 1'b0;
  case (i_rd_addr)
    `SYSREG_ADDR_USTATUS        : o_rd_data = r_ustatus;
    `SYSREG_ADDR_UIE            : o_rd_data = r_uie;
    `SYSREG_ADDR_UTVEC          : o_rd_data = r_utvec;
    `SYSREG_ADDR_VSTART         : o_rd_data = r_vstart;
    `SYSREG_ADDR_VXSAT          : o_rd_data = r_vxsat;
    `SYSREG_ADDR_VXRM           : o_rd_data = r_vxrm;
    `SYSREG_ADDR_USCRATCH       : o_rd_data = r_uscratch;
    `SYSREG_ADDR_UEPC           : o_rd_data = r_uepc;
    `SYSREG_ADDR_UCAUSE         : o_rd_data = r_ucause;
    `SYSREG_ADDR_UBADADDR       : o_rd_data = r_ubadaddr;
    `SYSREG_ADDR_UIP            : o_rd_data = r_uip;
    `SYSREG_ADDR_FFLAGS         : o_rd_data = r_fflags;
    `SYSREG_ADDR_FRM            : o_rd_data = r_frm;
    `SYSREG_ADDR_FCSR           : o_rd_data = r_fcsr;
    `SYSREG_ADDR_CYCLE          : o_rd_data = r_cycle;
    `SYSREG_ADDR_INSTRET        : o_rd_data = r_instret;
    `SYSREG_ADDR_HPMCOUNTER3    : o_rd_data = r_hpmcounter3;
    `SYSREG_ADDR_HPMCOUNTER4    : o_rd_data = r_hpmcounter4;
    `SYSREG_ADDR_HPMCOUNTER5    : o_rd_data = r_hpmcounter5;
    `SYSREG_ADDR_HPMCOUNTER6    : o_rd_data = r_hpmcounter6;
    `SYSREG_ADDR_HPMCOUNTER7    : o_rd_data = r_hpmcounter7;
    `SYSREG_ADDR_HPMCOUNTER8    : o_rd_data = r_hpmcounter8;
    `SYSREG_ADDR_HPMCOUNTER9    : o_rd_data = r_hpmcounter9;
    `SYSREG_ADDR_HPMCOUNTER10   : o_rd_data = r_hpmcounter10;
    `SYSREG_ADDR_HPMCOUNTER11   : o_rd_data = r_hpmcounter11;
    `SYSREG_ADDR_HPMCOUNTER12   : o_rd_data = r_hpmcounter12;
    `SYSREG_ADDR_HPMCOUNTER13   : o_rd_data = r_hpmcounter13;
    `SYSREG_ADDR_HPMCOUNTER14   : o_rd_data = r_hpmcounter14;
    `SYSREG_ADDR_HPMCOUNTER15   : o_rd_data = r_hpmcounter15;
    `SYSREG_ADDR_HPMCOUNTER16   : o_rd_data = r_hpmcounter16;
    `SYSREG_ADDR_HPMCOUNTER17   : o_rd_data = r_hpmcounter17;
    `SYSREG_ADDR_HPMCOUNTER18   : o_rd_data = r_hpmcounter18;
    `SYSREG_ADDR_HPMCOUNTER19   : o_rd_data = r_hpmcounter19;
    `SYSREG_ADDR_HPMCOUNTER20   : o_rd_data = r_hpmcounter20;
    `SYSREG_ADDR_HPMCOUNTER21   : o_rd_data = r_hpmcounter21;
    `SYSREG_ADDR_HPMCOUNTER22   : o_rd_data = r_hpmcounter22;
    `SYSREG_ADDR_HPMCOUNTER23   : o_rd_data = r_hpmcounter23;
    `SYSREG_ADDR_HPMCOUNTER24   : o_rd_data = r_hpmcounter24;
    `SYSREG_ADDR_HPMCOUNTER25   : o_rd_data = r_hpmcounter25;
    `SYSREG_ADDR_HPMCOUNTER26   : o_rd_data = r_hpmcounter26;
    `SYSREG_ADDR_HPMCOUNTER27   : o_rd_data = r_hpmcounter27;
    `SYSREG_ADDR_HPMCOUNTER28   : o_rd_data = r_hpmcounter28;
    `SYSREG_ADDR_HPMCOUNTER29   : o_rd_data = r_hpmcounter29;
    `SYSREG_ADDR_HPMCOUNTER30   : o_rd_data = r_hpmcounter30;
    `SYSREG_ADDR_HPMCOUNTER31   : o_rd_data = r_hpmcounter31;
    `SYSREG_ADDR_CYCLEH         : o_rd_data = r_cycleh;
    `SYSREG_ADDR_TIMEH          : o_rd_data = r_timeh;
    `SYSREG_ADDR_INSTRETH       : o_rd_data = r_instreth;
    `SYSREG_ADDR_HPMCOUNTERH3   : o_rd_data = r_hpmcounterh3;
    `SYSREG_ADDR_HPMCOUNTERH4   : o_rd_data = r_hpmcounterh4;
    `SYSREG_ADDR_HPMCOUNTERH5   : o_rd_data = r_hpmcounterh5;
    `SYSREG_ADDR_HPMCOUNTERH6   : o_rd_data = r_hpmcounterh6;
    `SYSREG_ADDR_HPMCOUNTERH7   : o_rd_data = r_hpmcounterh7;
    `SYSREG_ADDR_HPMCOUNTERH8   : o_rd_data = r_hpmcounterh8;
    `SYSREG_ADDR_HPMCOUNTERH9   : o_rd_data = r_hpmcounterh9;
    `SYSREG_ADDR_HPMCOUNTERH10  : o_rd_data = r_hpmcounterh10;
    `SYSREG_ADDR_HPMCOUNTERH11  : o_rd_data = r_hpmcounterh11;
    `SYSREG_ADDR_HPMCOUNTERH12  : o_rd_data = r_hpmcounterh12;
    `SYSREG_ADDR_HPMCOUNTERH13  : o_rd_data = r_hpmcounterh13;
    `SYSREG_ADDR_HPMCOUNTERH14  : o_rd_data = r_hpmcounterh14;
    `SYSREG_ADDR_HPMCOUNTERH15  : o_rd_data = r_hpmcounterh15;
    `SYSREG_ADDR_HPMCOUNTERH16  : o_rd_data = r_hpmcounterh16;
    `SYSREG_ADDR_HPMCOUNTERH17  : o_rd_data = r_hpmcounterh17;
    `SYSREG_ADDR_HPMCOUNTERH18  : o_rd_data = r_hpmcounterh18;
    `SYSREG_ADDR_HPMCOUNTERH19  : o_rd_data = r_hpmcounterh19;
    `SYSREG_ADDR_HPMCOUNTERH20  : o_rd_data = r_hpmcounterh20;
    `SYSREG_ADDR_HPMCOUNTERH21  : o_rd_data = r_hpmcounterh21;
    `SYSREG_ADDR_HPMCOUNTERH22  : o_rd_data = r_hpmcounterh22;
    `SYSREG_ADDR_HPMCOUNTERH23  : o_rd_data = r_hpmcounterh23;
    `SYSREG_ADDR_HPMCOUNTERH24  : o_rd_data = r_hpmcounterh24;
    `SYSREG_ADDR_HPMCOUNTERH25  : o_rd_data = r_hpmcounterh25;
    `SYSREG_ADDR_HPMCOUNTERH26  : o_rd_data = r_hpmcounterh26;
    `SYSREG_ADDR_HPMCOUNTERH27  : o_rd_data = r_hpmcounterh27;
    `SYSREG_ADDR_HPMCOUNTERH28  : o_rd_data = r_hpmcounterh28;
    `SYSREG_ADDR_HPMCOUNTERH29  : o_rd_data = r_hpmcounterh29;
    `SYSREG_ADDR_HPMCOUNTERH30  : o_rd_data = r_hpmcounterh30;
    `SYSREG_ADDR_HPMCOUNTERH31  : o_rd_data = r_hpmcounterh31;
    `SYSREG_ADDR_SSTATUS        : o_rd_data = r_sstatus;
    `SYSREG_ADDR_SEDELEG        : o_rd_data = r_sedeleg;
    `SYSREG_ADDR_SIDELEG        : o_rd_data = r_sideleg;
    `SYSREG_ADDR_SIE            : o_rd_data = r_sie;
    `SYSREG_ADDR_STVEC          : o_rd_data = r_stvec;
    `SYSREG_ADDR_SCOUNTEREN     : o_rd_data = r_scounteren;
    `SYSREG_ADDR_SSCRATCH       : o_rd_data = r_sscratch;
    `SYSREG_ADDR_SEPC           : o_rd_data = r_sepc;
    `SYSREG_ADDR_SCAUSE         : o_rd_data = r_scause;
    `SYSREG_ADDR_STVAL          : o_rd_data = r_stval;
    `SYSREG_ADDR_SIP            : o_rd_data = r_sip;
    `SYSREG_ADDR_SATP           : o_rd_data = r_satp;
    `SYSREG_ADDR_HSTATUS        : o_rd_data = r_hstatus;
    `SYSREG_ADDR_HEDELEG        : o_rd_data = r_hedeleg;
    `SYSREG_ADDR_HIDELEG        : o_rd_data = r_hideleg;
    `SYSREG_ADDR_HIE            : o_rd_data = r_hie;
    `SYSREG_ADDR_HTVEC          : o_rd_data = r_htvec;
    `SYSREG_ADDR_HSCRATCH       : o_rd_data = r_hscratch;
    `SYSREG_ADDR_HEPC           : o_rd_data = r_hepc;
    `SYSREG_ADDR_HCAUSE         : o_rd_data = r_hcause;
    `SYSREG_ADDR_HBADADDR       : o_rd_data = r_hbadaddr;
    `SYSREG_ADDR_HIP            : o_rd_data = r_hip;
    `SYSREG_ADDR_HPTBR          : o_rd_data = r_hptbr;
    `SYSREG_ADDR_MVENDORID      : o_rd_data = r_mvendorid;
    `SYSREG_ADDR_MARCHID        : o_rd_data = r_marchid;
    `SYSREG_ADDR_MIMPID         : o_rd_data = r_mimpid;
    `SYSREG_ADDR_MHARTID        : o_rd_data = r_mhartid;
    `SYSREG_ADDR_MSTATUS        : o_rd_data = r_mstatus;
    `SYSREG_ADDR_MISA           : o_rd_data = r_misa;
    `SYSREG_ADDR_MEDELEG        : o_rd_data = r_medeleg;
    `SYSREG_ADDR_MIDELEG        : o_rd_data = r_mideleg;
    `SYSREG_ADDR_MIE            : o_rd_data = r_mie;
    `SYSREG_ADDR_MTVEC          : o_rd_data = r_mtvec;
    `SYSREG_ADDR_MCOUNTEREN     : o_rd_data = r_mcounteren;
    `SYSREG_ADDR_MSCRATCH       : o_rd_data = r_mscratch;
    `SYSREG_ADDR_MEPC           : o_rd_data = r_mepc;
    `SYSREG_ADDR_MCAUSE         : o_rd_data = r_mcause;
    `SYSREG_ADDR_MTVAL          : o_rd_data = r_mtval;
    `SYSREG_ADDR_MIP            : o_rd_data = r_mip;
    `SYSREG_ADDR_MBASE          : o_rd_data = r_mbase;
    `SYSREG_ADDR_MBOUND         : o_rd_data = r_mbound;
    `SYSREG_ADDR_MIBASE         : o_rd_data = r_mibase;
    `SYSREG_ADDR_MIBOUND        : o_rd_data = r_mibound;
    `SYSREG_ADDR_MDBASE         : o_rd_data = r_mdbase;
    `SYSREG_ADDR_MDBOUND        : o_rd_data = r_mdbound;
    `SYSREG_ADDR_MCYCLE         : o_rd_data = r_mcycle;
    `SYSREG_ADDR_MINSTRET       : o_rd_data = r_minstret;
    `SYSREG_ADDR_MHPMCOUNTER3   : o_rd_data = r_mhpmcounter3;
    `SYSREG_ADDR_MHPMCOUNTER4   : o_rd_data = r_mhpmcounter4;
    `SYSREG_ADDR_MHPMCOUNTER5   : o_rd_data = r_mhpmcounter5;
    `SYSREG_ADDR_MHPMCOUNTER6   : o_rd_data = r_mhpmcounter6;
    `SYSREG_ADDR_MHPMCOUNTER7   : o_rd_data = r_mhpmcounter7;
    `SYSREG_ADDR_MHPMCOUNTER8   : o_rd_data = r_mhpmcounter8;
    `SYSREG_ADDR_MHPMCOUNTER9   : o_rd_data = r_mhpmcounter9;
    `SYSREG_ADDR_MHPMCOUNTER10  : o_rd_data = r_mhpmcounter10;
    `SYSREG_ADDR_MHPMCOUNTER11  : o_rd_data = r_mhpmcounter11;
    `SYSREG_ADDR_MHPMCOUNTER12  : o_rd_data = r_mhpmcounter12;
    `SYSREG_ADDR_MHPMCOUNTER13  : o_rd_data = r_mhpmcounter13;
    `SYSREG_ADDR_MHPMCOUNTER14  : o_rd_data = r_mhpmcounter14;
    `SYSREG_ADDR_MHPMCOUNTER15  : o_rd_data = r_mhpmcounter15;
    `SYSREG_ADDR_MHPMCOUNTER16  : o_rd_data = r_mhpmcounter16;
    `SYSREG_ADDR_MHPMCOUNTER17  : o_rd_data = r_mhpmcounter17;
    `SYSREG_ADDR_MHPMCOUNTER18  : o_rd_data = r_mhpmcounter18;
    `SYSREG_ADDR_MHPMCOUNTER19  : o_rd_data = r_mhpmcounter19;
    `SYSREG_ADDR_MHPMCOUNTER20  : o_rd_data = r_mhpmcounter20;
    `SYSREG_ADDR_MHPMCOUNTER21  : o_rd_data = r_mhpmcounter21;
    `SYSREG_ADDR_MHPMCOUNTER22  : o_rd_data = r_mhpmcounter22;
    `SYSREG_ADDR_MHPMCOUNTER23  : o_rd_data = r_mhpmcounter23;
    `SYSREG_ADDR_MHPMCOUNTER24  : o_rd_data = r_mhpmcounter24;
    `SYSREG_ADDR_MHPMCOUNTER25  : o_rd_data = r_mhpmcounter25;
    `SYSREG_ADDR_MHPMCOUNTER26  : o_rd_data = r_mhpmcounter26;
    `SYSREG_ADDR_MHPMCOUNTER27  : o_rd_data = r_mhpmcounter27;
    `SYSREG_ADDR_MHPMCOUNTER28  : o_rd_data = r_mhpmcounter28;
    `SYSREG_ADDR_MHPMCOUNTER29  : o_rd_data = r_mhpmcounter29;
    `SYSREG_ADDR_MHPMCOUNTER30  : o_rd_data = r_mhpmcounter30;
    `SYSREG_ADDR_MHPMCOUNTER31  : o_rd_data = r_mhpmcounter31;
    `SYSREG_ADDR_MHPEVENT3      : o_rd_data = r_mhpevent3;
    `SYSREG_ADDR_MHPEVENT4      : o_rd_data = r_mhpevent4;
    `SYSREG_ADDR_MHPEVENT5      : o_rd_data = r_mhpevent5;
    `SYSREG_ADDR_MHPEVENT6      : o_rd_data = r_mhpevent6;
    `SYSREG_ADDR_MHPEVENT7      : o_rd_data = r_mhpevent7;
    `SYSREG_ADDR_MHPEVENT8      : o_rd_data = r_mhpevent8;
    `SYSREG_ADDR_MHPEVENT9      : o_rd_data = r_mhpevent9;
    `SYSREG_ADDR_MHPEVENT10     : o_rd_data = r_mhpevent10;
    `SYSREG_ADDR_MHPEVENT11     : o_rd_data = r_mhpevent11;
    `SYSREG_ADDR_MHPEVENT12     : o_rd_data = r_mhpevent12;
    `SYSREG_ADDR_MHPEVENT13     : o_rd_data = r_mhpevent13;
    `SYSREG_ADDR_MHPEVENT14     : o_rd_data = r_mhpevent14;
    `SYSREG_ADDR_MHPEVENT15     : o_rd_data = r_mhpevent15;
    `SYSREG_ADDR_MHPEVENT16     : o_rd_data = r_mhpevent16;
    `SYSREG_ADDR_MHPEVENT17     : o_rd_data = r_mhpevent17;
    `SYSREG_ADDR_MHPEVENT18     : o_rd_data = r_mhpevent18;
    `SYSREG_ADDR_MHPEVENT19     : o_rd_data = r_mhpevent19;
    `SYSREG_ADDR_MHPEVENT20     : o_rd_data = r_mhpevent20;
    `SYSREG_ADDR_MHPEVENT21     : o_rd_data = r_mhpevent21;
    `SYSREG_ADDR_MHPEVENT22     : o_rd_data = r_mhpevent22;
    `SYSREG_ADDR_MHPEVENT23     : o_rd_data = r_mhpevent23;
    `SYSREG_ADDR_MHPEVENT24     : o_rd_data = r_mhpevent24;
    `SYSREG_ADDR_MHPEVENT25     : o_rd_data = r_mhpevent25;
    `SYSREG_ADDR_MHPEVENT26     : o_rd_data = r_mhpevent26;
    `SYSREG_ADDR_MHPEVENT27     : o_rd_data = r_mhpevent27;
    `SYSREG_ADDR_MHPEVENT28     : o_rd_data = r_mhpevent28;
    `SYSREG_ADDR_MHPEVENT29     : o_rd_data = r_mhpevent29;
    `SYSREG_ADDR_MHPEVENT30     : o_rd_data = r_mhpevent30;
    `SYSREG_ADDR_MHPEVENT31     : o_rd_data = r_mhpevent31;
    `SYSREG_ADDR_PMPCFG0        : o_rd_data = r_pmpcfg0;
    `SYSREG_ADDR_PMPCFG1        : o_rd_data = r_pmpcfg1;
    `SYSREG_ADDR_PMPCFG2        : o_rd_data = r_pmpcfg2;
    `SYSREG_ADDR_PMPCFG3        : o_rd_data = r_pmpcfg3;
    `SYSREG_ADDR_PMPADDR0       : o_rd_data = r_pmpaddr0;
    `SYSREG_ADDR_PMPADDR1       : o_rd_data = r_pmpaddr1;
    `SYSREG_ADDR_PMPADDR2       : o_rd_data = r_pmpaddr2;
    `SYSREG_ADDR_PMPADDR3       : o_rd_data = r_pmpaddr3;
    `SYSREG_ADDR_PMPADDR4       : o_rd_data = r_pmpaddr4;
    `SYSREG_ADDR_PMPADDR5       : o_rd_data = r_pmpaddr5;
    `SYSREG_ADDR_PMPADDR6       : o_rd_data = r_pmpaddr6;
    `SYSREG_ADDR_PMPADDR7       : o_rd_data = r_pmpaddr7;
    `SYSREG_ADDR_PMPADDR8       : o_rd_data = r_pmpaddr8;
    `SYSREG_ADDR_PMPADDR9       : o_rd_data = r_pmpaddr9;
    `SYSREG_ADDR_PMPADDR10      : o_rd_data = r_pmpaddr10;
    `SYSREG_ADDR_PMPADDR11      : o_rd_data = r_pmpaddr11;
    `SYSREG_ADDR_PMPADDR12      : o_rd_data = r_pmpaddr12;
    `SYSREG_ADDR_PMPADDR13      : o_rd_data = r_pmpaddr13;
    `SYSREG_ADDR_PMPADDR14      : o_rd_data = r_pmpaddr14;
    `SYSREG_ADDR_PMPADDR15      : o_rd_data = r_pmpaddr15;
    `SYSREG_ADDR_STATS          : o_rd_data = r_stats;
    default : begin
      o_rd_data = {riscv_pkg::XLEN_W{1'bx}};
      o_xcpt = 1'b1;
    end
  endcase // case (i_rd_addr)
end // always_comb

always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_ustatus       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_USTATUS       ) begin r_ustatus       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uie           <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_UIE           ) begin r_uie           <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_utvec         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_UTVEC         ) begin r_utvec         <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_vstart        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_VSTART        ) begin r_vstart        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_vxsat         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_VXSAT         ) begin r_vxsat         <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_vxrm          <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_VXRM          ) begin r_vxrm          <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uscratch      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_USCRATCH      ) begin r_uscratch      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uepc          <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_UEPC          ) begin r_uepc          <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_ucause        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_UCAUSE        ) begin r_ucause        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_ubadaddr      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_UBADADDR      ) begin r_ubadaddr      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uip           <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_UIP           ) begin r_uip           <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_fflags        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_FFLAGS        ) begin r_fflags        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_frm           <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_FRM           ) begin r_frm           <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_fcsr          <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_FCSR          ) begin r_fcsr          <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_cycle         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_CYCLE         ) begin r_cycle         <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_instret       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_INSTRET       ) begin r_instret       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter3   <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER3   ) begin r_hpmcounter3   <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter4   <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER4   ) begin r_hpmcounter4   <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter5   <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER5   ) begin r_hpmcounter5   <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter6   <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER6   ) begin r_hpmcounter6   <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter7   <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER7   ) begin r_hpmcounter7   <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter8   <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER8   ) begin r_hpmcounter8   <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter9   <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER9   ) begin r_hpmcounter9   <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter10  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER10  ) begin r_hpmcounter10  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter11  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER11  ) begin r_hpmcounter11  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter12  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER12  ) begin r_hpmcounter12  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter13  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER13  ) begin r_hpmcounter13  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter14  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER14  ) begin r_hpmcounter14  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter15  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER15  ) begin r_hpmcounter15  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter16  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER16  ) begin r_hpmcounter16  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter17  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER17  ) begin r_hpmcounter17  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter18  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER18  ) begin r_hpmcounter18  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter19  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER19  ) begin r_hpmcounter19  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter20  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER20  ) begin r_hpmcounter20  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter21  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER21  ) begin r_hpmcounter21  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter22  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER22  ) begin r_hpmcounter22  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter23  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER23  ) begin r_hpmcounter23  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter24  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER24  ) begin r_hpmcounter24  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter25  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER25  ) begin r_hpmcounter25  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter26  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER26  ) begin r_hpmcounter26  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter27  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER27  ) begin r_hpmcounter27  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter28  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER28  ) begin r_hpmcounter28  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter29  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER29  ) begin r_hpmcounter29  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter30  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER30  ) begin r_hpmcounter30  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter31  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTER31  ) begin r_hpmcounter31  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_cycleh        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_CYCLEH        ) begin r_cycleh        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_timeh         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_TIMEH         ) begin r_timeh         <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_instreth      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_INSTRETH      ) begin r_instreth      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh3  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH3  ) begin r_hpmcounterh3  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh4  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH4  ) begin r_hpmcounterh4  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh5  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH5  ) begin r_hpmcounterh5  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh6  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH6  ) begin r_hpmcounterh6  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh7  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH7  ) begin r_hpmcounterh7  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh8  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH8  ) begin r_hpmcounterh8  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh9  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH9  ) begin r_hpmcounterh9  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh10 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH10 ) begin r_hpmcounterh10 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh11 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH11 ) begin r_hpmcounterh11 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh12 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH12 ) begin r_hpmcounterh12 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh13 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH13 ) begin r_hpmcounterh13 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh14 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH14 ) begin r_hpmcounterh14 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh15 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH15 ) begin r_hpmcounterh15 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh16 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH16 ) begin r_hpmcounterh16 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh17 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH17 ) begin r_hpmcounterh17 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh18 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH18 ) begin r_hpmcounterh18 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh19 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH19 ) begin r_hpmcounterh19 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh20 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH20 ) begin r_hpmcounterh20 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh21 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH21 ) begin r_hpmcounterh21 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh22 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH22 ) begin r_hpmcounterh22 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh23 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH23 ) begin r_hpmcounterh23 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh24 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH24 ) begin r_hpmcounterh24 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh25 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH25 ) begin r_hpmcounterh25 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh26 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH26 ) begin r_hpmcounterh26 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh27 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH27 ) begin r_hpmcounterh27 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh28 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH28 ) begin r_hpmcounterh28 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh29 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH29 ) begin r_hpmcounterh29 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh30 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH30 ) begin r_hpmcounterh30 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh31 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPMCOUNTERH31 ) begin r_hpmcounterh31 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sstatus       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_SSTATUS       ) begin r_sstatus       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sedeleg       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_SEDELEG       ) begin r_sedeleg       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sideleg       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_SIDELEG       ) begin r_sideleg       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sie           <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_SIE           ) begin r_sie           <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_stvec         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_STVEC         ) begin r_stvec         <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_scounteren    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_SCOUNTEREN    ) begin r_scounteren    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sscratch      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_SSCRATCH      ) begin r_sscratch      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sepc          <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_SEPC          ) begin r_sepc          <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_scause        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_SCAUSE        ) begin r_scause        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_stval         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_STVAL         ) begin r_stval         <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sip           <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_SIP           ) begin r_sip           <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_satp          <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_SATP          ) begin r_satp          <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hstatus       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HSTATUS       ) begin r_hstatus       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hedeleg       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HEDELEG       ) begin r_hedeleg       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hideleg       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HIDELEG       ) begin r_hideleg       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hie           <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HIE           ) begin r_hie           <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_htvec         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HTVEC         ) begin r_htvec         <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hscratch      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HSCRATCH      ) begin r_hscratch      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hepc          <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HEPC          ) begin r_hepc          <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hcause        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HCAUSE        ) begin r_hcause        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hbadaddr      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HBADADDR      ) begin r_hbadaddr      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hip           <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HIP           ) begin r_hip           <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hptbr         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_HPTBR         ) begin r_hptbr         <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mvendorid     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MVENDORID     ) begin r_mvendorid     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_marchid       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MARCHID       ) begin r_marchid       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mimpid        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MIMPID        ) begin r_mimpid        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhartid       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHARTID       ) begin r_mhartid       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mstatus       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MSTATUS       ) begin r_mstatus       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_misa          <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MISA          ) begin r_misa          <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_medeleg       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MEDELEG       ) begin r_medeleg       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mideleg       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MIDELEG       ) begin r_mideleg       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mie           <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MIE           ) begin r_mie           <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mtvec         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MTVEC         ) begin r_mtvec         <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mcounteren    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MCOUNTEREN    ) begin r_mcounteren    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mscratch      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MSCRATCH      ) begin r_mscratch      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mepc          <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MEPC          ) begin r_mepc          <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mcause        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MCAUSE        ) begin r_mcause        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mtval         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MTVAL         ) begin r_mtval         <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mip           <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MIP           ) begin r_mip           <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mbase         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MBASE         ) begin r_mbase         <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mbound        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MBOUND        ) begin r_mbound        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mibase        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MIBASE        ) begin r_mibase        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mibound       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MIBOUND       ) begin r_mibound       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mdbase        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MDBASE        ) begin r_mdbase        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mdbound       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MDBOUND       ) begin r_mdbound       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mcycle        <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MCYCLE        ) begin r_mcycle        <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_minstret      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MINSTRET      ) begin r_minstret      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter3  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER3  ) begin r_mhpmcounter3  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter4  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER4  ) begin r_mhpmcounter4  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter5  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER5  ) begin r_mhpmcounter5  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter6  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER6  ) begin r_mhpmcounter6  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter7  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER7  ) begin r_mhpmcounter7  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter8  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER8  ) begin r_mhpmcounter8  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter9  <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER9  ) begin r_mhpmcounter9  <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter10 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER10 ) begin r_mhpmcounter10 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter11 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER11 ) begin r_mhpmcounter11 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter12 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER12 ) begin r_mhpmcounter12 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter13 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER13 ) begin r_mhpmcounter13 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter14 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER14 ) begin r_mhpmcounter14 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter15 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER15 ) begin r_mhpmcounter15 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter16 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER16 ) begin r_mhpmcounter16 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter17 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER17 ) begin r_mhpmcounter17 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter18 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER18 ) begin r_mhpmcounter18 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter19 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER19 ) begin r_mhpmcounter19 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter20 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER20 ) begin r_mhpmcounter20 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter21 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER21 ) begin r_mhpmcounter21 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter22 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER22 ) begin r_mhpmcounter22 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter23 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER23 ) begin r_mhpmcounter23 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter24 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER24 ) begin r_mhpmcounter24 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter25 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER25 ) begin r_mhpmcounter25 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter26 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER26 ) begin r_mhpmcounter26 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter27 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER27 ) begin r_mhpmcounter27 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter28 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER28 ) begin r_mhpmcounter28 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter29 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER29 ) begin r_mhpmcounter29 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter30 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER30 ) begin r_mhpmcounter30 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter31 <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPMCOUNTER31 ) begin r_mhpmcounter31 <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent3     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT3     ) begin r_mhpevent3     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent4     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT4     ) begin r_mhpevent4     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent5     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT5     ) begin r_mhpevent5     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent6     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT6     ) begin r_mhpevent6     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent7     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT7     ) begin r_mhpevent7     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent8     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT8     ) begin r_mhpevent8     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent9     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT9     ) begin r_mhpevent9     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent10    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT10    ) begin r_mhpevent10    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent11    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT11    ) begin r_mhpevent11    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent12    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT12    ) begin r_mhpevent12    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent13    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT13    ) begin r_mhpevent13    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent14    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT14    ) begin r_mhpevent14    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent15    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT15    ) begin r_mhpevent15    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent16    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT16    ) begin r_mhpevent16    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent17    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT17    ) begin r_mhpevent17    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent18    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT18    ) begin r_mhpevent18    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent19    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT19    ) begin r_mhpevent19    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent20    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT20    ) begin r_mhpevent20    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent21    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT21    ) begin r_mhpevent21    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent22    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT22    ) begin r_mhpevent22    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent23    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT23    ) begin r_mhpevent23    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent24    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT24    ) begin r_mhpevent24    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent25    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT25    ) begin r_mhpevent25    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent26    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT26    ) begin r_mhpevent26    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent27    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT27    ) begin r_mhpevent27    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent28    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT28    ) begin r_mhpevent28    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent29    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT29    ) begin r_mhpevent29    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent30    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT30    ) begin r_mhpevent30    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent31    <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_MHPEVENT31    ) begin r_mhpevent31    <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg0       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPCFG0       ) begin r_pmpcfg0       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg1       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPCFG1       ) begin r_pmpcfg1       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg2       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPCFG2       ) begin r_pmpcfg2       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg3       <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPCFG3       ) begin r_pmpcfg3       <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr0      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR0      ) begin r_pmpaddr0      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr1      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR1      ) begin r_pmpaddr1      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr2      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR2      ) begin r_pmpaddr2      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr3      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR3      ) begin r_pmpaddr3      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr4      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR4      ) begin r_pmpaddr4      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr5      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR5      ) begin r_pmpaddr5      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr6      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR6      ) begin r_pmpaddr6      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr7      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR7      ) begin r_pmpaddr7      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr8      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR8      ) begin r_pmpaddr8      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr9      <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR9      ) begin r_pmpaddr9      <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr10     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR10     ) begin r_pmpaddr10     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr11     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR11     ) begin r_pmpaddr11     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr12     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR12     ) begin r_pmpaddr12     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr13     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR13     ) begin r_pmpaddr13     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr14     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR14     ) begin r_pmpaddr14     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr15     <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_PMPADDR15     ) begin r_pmpaddr15     <= i_wr_data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_stats         <= 'h0; end else if (i_wr_vld & i_wr_addr ==  `SYSREG_ADDR_STATS         ) begin r_stats         <= i_wr_data; end end

endmodule // msrh_csr
