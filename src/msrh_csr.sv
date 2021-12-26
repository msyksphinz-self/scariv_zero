module msrh_csr
  import riscv_pkg::*;
  (
   input logic                i_clk,
   input logic                i_reset_n,

   csr_rd_if.slave            read_if,
   csr_wr_if.slave            write_if,

   /* CSR information */
   csr_info_if.master         csr_info,

   // Commit notification
   input msrh_pkg::commit_blk_t i_commit,

   output logic               o_xcpt
   );

`include "msrh_csr_def.svh"

msrh_pkg::priv_t    r_priv, w_priv_next;

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
logic [XLEN_W-1: 0] r_sedeleg;
logic [XLEN_W-1: 0] r_sideleg;
logic [XLEN_W-1: 0] r_sie;
logic [XLEN_W-1: 0] r_stvec;
logic [XLEN_W-1: 0] r_scounteren;
logic [XLEN_W-1: 0] r_sscratch;
logic [XLEN_W-1: 0] r_sepc, w_sepc_next;
logic [XLEN_W-1: 0] r_scause, w_scause_next;
logic [XLEN_W-1: 0] r_stval, w_stval_next;
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
logic [riscv_pkg::XLEN_W-1: 0] w_mstatus, w_mstatus_next;
logic [XLEN_W-1: 0] r_mstatus;
logic [XLEN_W-1: 0] r_misa;
logic [XLEN_W-1: 0] r_medeleg;
logic [XLEN_W-1: 0] r_mideleg;
logic [XLEN_W-1: 0] r_mie;
logic [XLEN_W-1: 0] r_mtvec;
logic [XLEN_W-1: 0] r_mcounteren;
logic [XLEN_W-1: 0] r_mscratch;
logic [XLEN_W-1: 0] r_mepc,   w_mepc_next;
logic [XLEN_W-1: 0] r_mcause, w_mcause_next;
logic [XLEN_W-1: 0] r_mtval,  w_mtval_next;
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
  case (read_if.addr)
    `SYSREG_ADDR_USTATUS        : read_if.data = r_ustatus;
    `SYSREG_ADDR_UIE            : read_if.data = r_uie;
    `SYSREG_ADDR_UTVEC          : read_if.data = r_utvec;
    `SYSREG_ADDR_VSTART         : read_if.data = r_vstart;
    `SYSREG_ADDR_VXSAT          : read_if.data = r_vxsat;
    `SYSREG_ADDR_VXRM           : read_if.data = r_vxrm;
    `SYSREG_ADDR_USCRATCH       : read_if.data = r_uscratch;
    `SYSREG_ADDR_UEPC           : read_if.data = r_uepc;
    `SYSREG_ADDR_UCAUSE         : read_if.data = r_ucause;
    `SYSREG_ADDR_UBADADDR       : read_if.data = r_ubadaddr;
    `SYSREG_ADDR_UIP            : read_if.data = r_uip;
    `SYSREG_ADDR_FFLAGS         : read_if.data = r_fflags;
    `SYSREG_ADDR_FRM            : read_if.data = r_frm;
    `SYSREG_ADDR_FCSR           : read_if.data = r_fcsr;
    `SYSREG_ADDR_CYCLE          : read_if.data = r_cycle;
    `SYSREG_ADDR_INSTRET        : read_if.data = r_instret;
    `SYSREG_ADDR_HPMCOUNTER3    : read_if.data = r_hpmcounter3;
    `SYSREG_ADDR_HPMCOUNTER4    : read_if.data = r_hpmcounter4;
    `SYSREG_ADDR_HPMCOUNTER5    : read_if.data = r_hpmcounter5;
    `SYSREG_ADDR_HPMCOUNTER6    : read_if.data = r_hpmcounter6;
    `SYSREG_ADDR_HPMCOUNTER7    : read_if.data = r_hpmcounter7;
    `SYSREG_ADDR_HPMCOUNTER8    : read_if.data = r_hpmcounter8;
    `SYSREG_ADDR_HPMCOUNTER9    : read_if.data = r_hpmcounter9;
    `SYSREG_ADDR_HPMCOUNTER10   : read_if.data = r_hpmcounter10;
    `SYSREG_ADDR_HPMCOUNTER11   : read_if.data = r_hpmcounter11;
    `SYSREG_ADDR_HPMCOUNTER12   : read_if.data = r_hpmcounter12;
    `SYSREG_ADDR_HPMCOUNTER13   : read_if.data = r_hpmcounter13;
    `SYSREG_ADDR_HPMCOUNTER14   : read_if.data = r_hpmcounter14;
    `SYSREG_ADDR_HPMCOUNTER15   : read_if.data = r_hpmcounter15;
    `SYSREG_ADDR_HPMCOUNTER16   : read_if.data = r_hpmcounter16;
    `SYSREG_ADDR_HPMCOUNTER17   : read_if.data = r_hpmcounter17;
    `SYSREG_ADDR_HPMCOUNTER18   : read_if.data = r_hpmcounter18;
    `SYSREG_ADDR_HPMCOUNTER19   : read_if.data = r_hpmcounter19;
    `SYSREG_ADDR_HPMCOUNTER20   : read_if.data = r_hpmcounter20;
    `SYSREG_ADDR_HPMCOUNTER21   : read_if.data = r_hpmcounter21;
    `SYSREG_ADDR_HPMCOUNTER22   : read_if.data = r_hpmcounter22;
    `SYSREG_ADDR_HPMCOUNTER23   : read_if.data = r_hpmcounter23;
    `SYSREG_ADDR_HPMCOUNTER24   : read_if.data = r_hpmcounter24;
    `SYSREG_ADDR_HPMCOUNTER25   : read_if.data = r_hpmcounter25;
    `SYSREG_ADDR_HPMCOUNTER26   : read_if.data = r_hpmcounter26;
    `SYSREG_ADDR_HPMCOUNTER27   : read_if.data = r_hpmcounter27;
    `SYSREG_ADDR_HPMCOUNTER28   : read_if.data = r_hpmcounter28;
    `SYSREG_ADDR_HPMCOUNTER29   : read_if.data = r_hpmcounter29;
    `SYSREG_ADDR_HPMCOUNTER30   : read_if.data = r_hpmcounter30;
    `SYSREG_ADDR_HPMCOUNTER31   : read_if.data = r_hpmcounter31;
    `SYSREG_ADDR_CYCLEH         : read_if.data = r_cycleh;
    `SYSREG_ADDR_TIMEH          : read_if.data = r_timeh;
    `SYSREG_ADDR_INSTRETH       : read_if.data = r_instreth;
    `SYSREG_ADDR_HPMCOUNTERH3   : read_if.data = r_hpmcounterh3;
    `SYSREG_ADDR_HPMCOUNTERH4   : read_if.data = r_hpmcounterh4;
    `SYSREG_ADDR_HPMCOUNTERH5   : read_if.data = r_hpmcounterh5;
    `SYSREG_ADDR_HPMCOUNTERH6   : read_if.data = r_hpmcounterh6;
    `SYSREG_ADDR_HPMCOUNTERH7   : read_if.data = r_hpmcounterh7;
    `SYSREG_ADDR_HPMCOUNTERH8   : read_if.data = r_hpmcounterh8;
    `SYSREG_ADDR_HPMCOUNTERH9   : read_if.data = r_hpmcounterh9;
    `SYSREG_ADDR_HPMCOUNTERH10  : read_if.data = r_hpmcounterh10;
    `SYSREG_ADDR_HPMCOUNTERH11  : read_if.data = r_hpmcounterh11;
    `SYSREG_ADDR_HPMCOUNTERH12  : read_if.data = r_hpmcounterh12;
    `SYSREG_ADDR_HPMCOUNTERH13  : read_if.data = r_hpmcounterh13;
    `SYSREG_ADDR_HPMCOUNTERH14  : read_if.data = r_hpmcounterh14;
    `SYSREG_ADDR_HPMCOUNTERH15  : read_if.data = r_hpmcounterh15;
    `SYSREG_ADDR_HPMCOUNTERH16  : read_if.data = r_hpmcounterh16;
    `SYSREG_ADDR_HPMCOUNTERH17  : read_if.data = r_hpmcounterh17;
    `SYSREG_ADDR_HPMCOUNTERH18  : read_if.data = r_hpmcounterh18;
    `SYSREG_ADDR_HPMCOUNTERH19  : read_if.data = r_hpmcounterh19;
    `SYSREG_ADDR_HPMCOUNTERH20  : read_if.data = r_hpmcounterh20;
    `SYSREG_ADDR_HPMCOUNTERH21  : read_if.data = r_hpmcounterh21;
    `SYSREG_ADDR_HPMCOUNTERH22  : read_if.data = r_hpmcounterh22;
    `SYSREG_ADDR_HPMCOUNTERH23  : read_if.data = r_hpmcounterh23;
    `SYSREG_ADDR_HPMCOUNTERH24  : read_if.data = r_hpmcounterh24;
    `SYSREG_ADDR_HPMCOUNTERH25  : read_if.data = r_hpmcounterh25;
    `SYSREG_ADDR_HPMCOUNTERH26  : read_if.data = r_hpmcounterh26;
    `SYSREG_ADDR_HPMCOUNTERH27  : read_if.data = r_hpmcounterh27;
    `SYSREG_ADDR_HPMCOUNTERH28  : read_if.data = r_hpmcounterh28;
    `SYSREG_ADDR_HPMCOUNTERH29  : read_if.data = r_hpmcounterh29;
    `SYSREG_ADDR_HPMCOUNTERH30  : read_if.data = r_hpmcounterh30;
    `SYSREG_ADDR_HPMCOUNTERH31  : read_if.data = r_hpmcounterh31;
    `SYSREG_ADDR_SSTATUS        : read_if.data = riscv_pkg::map_sstatus(r_mstatus);
    `SYSREG_ADDR_SEDELEG        : read_if.data = r_sedeleg;
    `SYSREG_ADDR_SIDELEG        : read_if.data = r_sideleg;
    `SYSREG_ADDR_SIE            : read_if.data = r_sie;
    `SYSREG_ADDR_STVEC          : read_if.data = r_stvec;
    `SYSREG_ADDR_SCOUNTEREN     : read_if.data = r_scounteren;
    `SYSREG_ADDR_SSCRATCH       : read_if.data = r_sscratch;
    `SYSREG_ADDR_SEPC           : read_if.data = r_sepc;
    `SYSREG_ADDR_SCAUSE         : read_if.data = r_scause;
    `SYSREG_ADDR_STVAL          : read_if.data = r_stval;
    `SYSREG_ADDR_SIP            : read_if.data = r_sip;
    `SYSREG_ADDR_SATP           : read_if.data = r_satp;
    `SYSREG_ADDR_HSTATUS        : read_if.data = r_hstatus;
    `SYSREG_ADDR_HEDELEG        : read_if.data = r_hedeleg;
    `SYSREG_ADDR_HIDELEG        : read_if.data = r_hideleg;
    `SYSREG_ADDR_HIE            : read_if.data = r_hie;
    `SYSREG_ADDR_HTVEC          : read_if.data = r_htvec;
    `SYSREG_ADDR_HSCRATCH       : read_if.data = r_hscratch;
    `SYSREG_ADDR_HEPC           : read_if.data = r_hepc;
    `SYSREG_ADDR_HCAUSE         : read_if.data = r_hcause;
    `SYSREG_ADDR_HBADADDR       : read_if.data = r_hbadaddr;
    `SYSREG_ADDR_HIP            : read_if.data = r_hip;
    `SYSREG_ADDR_HPTBR          : read_if.data = r_hptbr;
    `SYSREG_ADDR_MVENDORID      : read_if.data = r_mvendorid;
    `SYSREG_ADDR_MARCHID        : read_if.data = r_marchid;
    `SYSREG_ADDR_MIMPID         : read_if.data = r_mimpid;
    `SYSREG_ADDR_MHARTID        : read_if.data = r_mhartid;
    `SYSREG_ADDR_MSTATUS        : read_if.data = w_mstatus;
    `SYSREG_ADDR_MISA           : read_if.data = r_misa;
    `SYSREG_ADDR_MEDELEG        : read_if.data = r_medeleg;
    `SYSREG_ADDR_MIDELEG        : read_if.data = r_mideleg;
    `SYSREG_ADDR_MIE            : read_if.data = r_mie;
    `SYSREG_ADDR_MTVEC          : read_if.data = r_mtvec;
    `SYSREG_ADDR_MCOUNTEREN     : read_if.data = r_mcounteren;
    `SYSREG_ADDR_MSCRATCH       : read_if.data = r_mscratch;
    `SYSREG_ADDR_MEPC           : read_if.data = r_mepc;
    `SYSREG_ADDR_MCAUSE         : read_if.data = r_mcause;
    `SYSREG_ADDR_MTVAL          : read_if.data = r_mtval;
    `SYSREG_ADDR_MIP            : read_if.data = r_mip;
    `SYSREG_ADDR_MBASE          : read_if.data = r_mbase;
    `SYSREG_ADDR_MBOUND         : read_if.data = r_mbound;
    `SYSREG_ADDR_MIBASE         : read_if.data = r_mibase;
    `SYSREG_ADDR_MIBOUND        : read_if.data = r_mibound;
    `SYSREG_ADDR_MDBASE         : read_if.data = r_mdbase;
    `SYSREG_ADDR_MDBOUND        : read_if.data = r_mdbound;
    `SYSREG_ADDR_MCYCLE         : read_if.data = r_mcycle;
    `SYSREG_ADDR_MINSTRET       : read_if.data = r_minstret;
    `SYSREG_ADDR_MHPMCOUNTER3   : read_if.data = r_mhpmcounter3;
    `SYSREG_ADDR_MHPMCOUNTER4   : read_if.data = r_mhpmcounter4;
    `SYSREG_ADDR_MHPMCOUNTER5   : read_if.data = r_mhpmcounter5;
    `SYSREG_ADDR_MHPMCOUNTER6   : read_if.data = r_mhpmcounter6;
    `SYSREG_ADDR_MHPMCOUNTER7   : read_if.data = r_mhpmcounter7;
    `SYSREG_ADDR_MHPMCOUNTER8   : read_if.data = r_mhpmcounter8;
    `SYSREG_ADDR_MHPMCOUNTER9   : read_if.data = r_mhpmcounter9;
    `SYSREG_ADDR_MHPMCOUNTER10  : read_if.data = r_mhpmcounter10;
    `SYSREG_ADDR_MHPMCOUNTER11  : read_if.data = r_mhpmcounter11;
    `SYSREG_ADDR_MHPMCOUNTER12  : read_if.data = r_mhpmcounter12;
    `SYSREG_ADDR_MHPMCOUNTER13  : read_if.data = r_mhpmcounter13;
    `SYSREG_ADDR_MHPMCOUNTER14  : read_if.data = r_mhpmcounter14;
    `SYSREG_ADDR_MHPMCOUNTER15  : read_if.data = r_mhpmcounter15;
    `SYSREG_ADDR_MHPMCOUNTER16  : read_if.data = r_mhpmcounter16;
    `SYSREG_ADDR_MHPMCOUNTER17  : read_if.data = r_mhpmcounter17;
    `SYSREG_ADDR_MHPMCOUNTER18  : read_if.data = r_mhpmcounter18;
    `SYSREG_ADDR_MHPMCOUNTER19  : read_if.data = r_mhpmcounter19;
    `SYSREG_ADDR_MHPMCOUNTER20  : read_if.data = r_mhpmcounter20;
    `SYSREG_ADDR_MHPMCOUNTER21  : read_if.data = r_mhpmcounter21;
    `SYSREG_ADDR_MHPMCOUNTER22  : read_if.data = r_mhpmcounter22;
    `SYSREG_ADDR_MHPMCOUNTER23  : read_if.data = r_mhpmcounter23;
    `SYSREG_ADDR_MHPMCOUNTER24  : read_if.data = r_mhpmcounter24;
    `SYSREG_ADDR_MHPMCOUNTER25  : read_if.data = r_mhpmcounter25;
    `SYSREG_ADDR_MHPMCOUNTER26  : read_if.data = r_mhpmcounter26;
    `SYSREG_ADDR_MHPMCOUNTER27  : read_if.data = r_mhpmcounter27;
    `SYSREG_ADDR_MHPMCOUNTER28  : read_if.data = r_mhpmcounter28;
    `SYSREG_ADDR_MHPMCOUNTER29  : read_if.data = r_mhpmcounter29;
    `SYSREG_ADDR_MHPMCOUNTER30  : read_if.data = r_mhpmcounter30;
    `SYSREG_ADDR_MHPMCOUNTER31  : read_if.data = r_mhpmcounter31;
    `SYSREG_ADDR_MHPEVENT3      : read_if.data = r_mhpevent3;
    `SYSREG_ADDR_MHPEVENT4      : read_if.data = r_mhpevent4;
    `SYSREG_ADDR_MHPEVENT5      : read_if.data = r_mhpevent5;
    `SYSREG_ADDR_MHPEVENT6      : read_if.data = r_mhpevent6;
    `SYSREG_ADDR_MHPEVENT7      : read_if.data = r_mhpevent7;
    `SYSREG_ADDR_MHPEVENT8      : read_if.data = r_mhpevent8;
    `SYSREG_ADDR_MHPEVENT9      : read_if.data = r_mhpevent9;
    `SYSREG_ADDR_MHPEVENT10     : read_if.data = r_mhpevent10;
    `SYSREG_ADDR_MHPEVENT11     : read_if.data = r_mhpevent11;
    `SYSREG_ADDR_MHPEVENT12     : read_if.data = r_mhpevent12;
    `SYSREG_ADDR_MHPEVENT13     : read_if.data = r_mhpevent13;
    `SYSREG_ADDR_MHPEVENT14     : read_if.data = r_mhpevent14;
    `SYSREG_ADDR_MHPEVENT15     : read_if.data = r_mhpevent15;
    `SYSREG_ADDR_MHPEVENT16     : read_if.data = r_mhpevent16;
    `SYSREG_ADDR_MHPEVENT17     : read_if.data = r_mhpevent17;
    `SYSREG_ADDR_MHPEVENT18     : read_if.data = r_mhpevent18;
    `SYSREG_ADDR_MHPEVENT19     : read_if.data = r_mhpevent19;
    `SYSREG_ADDR_MHPEVENT20     : read_if.data = r_mhpevent20;
    `SYSREG_ADDR_MHPEVENT21     : read_if.data = r_mhpevent21;
    `SYSREG_ADDR_MHPEVENT22     : read_if.data = r_mhpevent22;
    `SYSREG_ADDR_MHPEVENT23     : read_if.data = r_mhpevent23;
    `SYSREG_ADDR_MHPEVENT24     : read_if.data = r_mhpevent24;
    `SYSREG_ADDR_MHPEVENT25     : read_if.data = r_mhpevent25;
    `SYSREG_ADDR_MHPEVENT26     : read_if.data = r_mhpevent26;
    `SYSREG_ADDR_MHPEVENT27     : read_if.data = r_mhpevent27;
    `SYSREG_ADDR_MHPEVENT28     : read_if.data = r_mhpevent28;
    `SYSREG_ADDR_MHPEVENT29     : read_if.data = r_mhpevent29;
    `SYSREG_ADDR_MHPEVENT30     : read_if.data = r_mhpevent30;
    `SYSREG_ADDR_MHPEVENT31     : read_if.data = r_mhpevent31;
    `SYSREG_ADDR_PMPCFG0        : read_if.data = r_pmpcfg0;
    `SYSREG_ADDR_PMPCFG1        : read_if.data = r_pmpcfg1;
    `SYSREG_ADDR_PMPCFG2        : read_if.data = r_pmpcfg2;
    `SYSREG_ADDR_PMPCFG3        : read_if.data = r_pmpcfg3;
    `SYSREG_ADDR_PMPADDR0       : read_if.data = r_pmpaddr0;
    `SYSREG_ADDR_PMPADDR1       : read_if.data = r_pmpaddr1;
    `SYSREG_ADDR_PMPADDR2       : read_if.data = r_pmpaddr2;
    `SYSREG_ADDR_PMPADDR3       : read_if.data = r_pmpaddr3;
    `SYSREG_ADDR_PMPADDR4       : read_if.data = r_pmpaddr4;
    `SYSREG_ADDR_PMPADDR5       : read_if.data = r_pmpaddr5;
    `SYSREG_ADDR_PMPADDR6       : read_if.data = r_pmpaddr6;
    `SYSREG_ADDR_PMPADDR7       : read_if.data = r_pmpaddr7;
    `SYSREG_ADDR_PMPADDR8       : read_if.data = r_pmpaddr8;
    `SYSREG_ADDR_PMPADDR9       : read_if.data = r_pmpaddr9;
    `SYSREG_ADDR_PMPADDR10      : read_if.data = r_pmpaddr10;
    `SYSREG_ADDR_PMPADDR11      : read_if.data = r_pmpaddr11;
    `SYSREG_ADDR_PMPADDR12      : read_if.data = r_pmpaddr12;
    `SYSREG_ADDR_PMPADDR13      : read_if.data = r_pmpaddr13;
    `SYSREG_ADDR_PMPADDR14      : read_if.data = r_pmpaddr14;
    `SYSREG_ADDR_PMPADDR15      : read_if.data = r_pmpaddr15;
    `SYSREG_ADDR_STATS          : read_if.data = r_stats;
    default : begin
      read_if.data = {riscv_pkg::XLEN_W{1'bx}};
      o_xcpt = 1'b1;
    end
  endcase // case (read_if.addr)
end // always_comb

always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_ustatus       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_USTATUS       ) begin r_ustatus       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uie           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UIE           ) begin r_uie           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_utvec         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UTVEC         ) begin r_utvec         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_vstart        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_VSTART        ) begin r_vstart        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_vxsat         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_VXSAT         ) begin r_vxsat         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_vxrm          <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_VXRM          ) begin r_vxrm          <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uscratch      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_USCRATCH      ) begin r_uscratch      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uepc          <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UEPC          ) begin r_uepc          <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_ucause        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UCAUSE        ) begin r_ucause        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_ubadaddr      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UBADADDR      ) begin r_ubadaddr      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_uip           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_UIP           ) begin r_uip           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_fflags        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_FFLAGS        ) begin r_fflags        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_frm           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_FRM           ) begin r_frm           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_fcsr          <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_FCSR          ) begin r_fcsr          <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_cycle         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_CYCLE         ) begin r_cycle         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_instret       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_INSTRET       ) begin r_instret       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter3   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER3   ) begin r_hpmcounter3   <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter4   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER4   ) begin r_hpmcounter4   <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter5   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER5   ) begin r_hpmcounter5   <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter6   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER6   ) begin r_hpmcounter6   <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter7   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER7   ) begin r_hpmcounter7   <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter8   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER8   ) begin r_hpmcounter8   <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter9   <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER9   ) begin r_hpmcounter9   <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter10  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER10  ) begin r_hpmcounter10  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter11  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER11  ) begin r_hpmcounter11  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter12  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER12  ) begin r_hpmcounter12  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter13  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER13  ) begin r_hpmcounter13  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter14  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER14  ) begin r_hpmcounter14  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter15  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER15  ) begin r_hpmcounter15  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter16  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER16  ) begin r_hpmcounter16  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter17  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER17  ) begin r_hpmcounter17  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter18  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER18  ) begin r_hpmcounter18  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter19  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER19  ) begin r_hpmcounter19  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter20  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER20  ) begin r_hpmcounter20  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter21  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER21  ) begin r_hpmcounter21  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter22  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER22  ) begin r_hpmcounter22  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter23  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER23  ) begin r_hpmcounter23  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter24  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER24  ) begin r_hpmcounter24  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter25  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER25  ) begin r_hpmcounter25  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter26  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER26  ) begin r_hpmcounter26  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter27  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER27  ) begin r_hpmcounter27  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter28  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER28  ) begin r_hpmcounter28  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter29  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER29  ) begin r_hpmcounter29  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter30  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER30  ) begin r_hpmcounter30  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounter31  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTER31  ) begin r_hpmcounter31  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_cycleh        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_CYCLEH        ) begin r_cycleh        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_timeh         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_TIMEH         ) begin r_timeh         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_instreth      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_INSTRETH      ) begin r_instreth      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh3  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH3  ) begin r_hpmcounterh3  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh4  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH4  ) begin r_hpmcounterh4  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh5  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH5  ) begin r_hpmcounterh5  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh6  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH6  ) begin r_hpmcounterh6  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh7  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH7  ) begin r_hpmcounterh7  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh8  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH8  ) begin r_hpmcounterh8  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh9  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH9  ) begin r_hpmcounterh9  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh10 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH10 ) begin r_hpmcounterh10 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh11 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH11 ) begin r_hpmcounterh11 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh12 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH12 ) begin r_hpmcounterh12 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh13 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH13 ) begin r_hpmcounterh13 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh14 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH14 ) begin r_hpmcounterh14 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh15 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH15 ) begin r_hpmcounterh15 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh16 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH16 ) begin r_hpmcounterh16 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh17 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH17 ) begin r_hpmcounterh17 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh18 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH18 ) begin r_hpmcounterh18 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh19 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH19 ) begin r_hpmcounterh19 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh20 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH20 ) begin r_hpmcounterh20 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh21 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH21 ) begin r_hpmcounterh21 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh22 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH22 ) begin r_hpmcounterh22 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh23 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH23 ) begin r_hpmcounterh23 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh24 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH24 ) begin r_hpmcounterh24 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh25 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH25 ) begin r_hpmcounterh25 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh26 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH26 ) begin r_hpmcounterh26 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh27 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH27 ) begin r_hpmcounterh27 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh28 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH28 ) begin r_hpmcounterh28 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh29 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH29 ) begin r_hpmcounterh29 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh30 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH30 ) begin r_hpmcounterh30 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hpmcounterh31 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPMCOUNTERH31 ) begin r_hpmcounterh31 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sedeleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SEDELEG       ) begin r_sedeleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sideleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SIDELEG       ) begin r_sideleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sie           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SIE           ) begin r_sie           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_stvec         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_STVEC         ) begin r_stvec         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_scounteren    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SCOUNTEREN    ) begin r_scounteren    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sscratch      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SSCRATCH      ) begin r_sscratch      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_sip           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SIP           ) begin r_sip           <= write_if.data; end end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_satp <= 'h0;
  end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_SATP) begin
    r_satp <= write_if.data;
  end
end

always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hstatus       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HSTATUS       ) begin r_hstatus       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hedeleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HEDELEG       ) begin r_hedeleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hideleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HIDELEG       ) begin r_hideleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hie           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HIE           ) begin r_hie           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_htvec         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HTVEC         ) begin r_htvec         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hscratch      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HSCRATCH      ) begin r_hscratch      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hepc          <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HEPC          ) begin r_hepc          <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hcause        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HCAUSE        ) begin r_hcause        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hbadaddr      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HBADADDR      ) begin r_hbadaddr      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hip           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HIP           ) begin r_hip           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_hptbr         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_HPTBR         ) begin r_hptbr         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mvendorid     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MVENDORID     ) begin r_mvendorid     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_marchid       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MARCHID       ) begin r_marchid       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mimpid        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MIMPID        ) begin r_mimpid        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhartid       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHARTID       ) begin r_mhartid       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_misa          <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MISA          ) begin r_misa          <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_medeleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MEDELEG       ) begin r_medeleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mideleg       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MIDELEG       ) begin r_mideleg       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mie           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MIE           ) begin r_mie           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mtvec         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MTVEC         ) begin r_mtvec         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mcounteren    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MCOUNTEREN    ) begin r_mcounteren    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mscratch      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MSCRATCH      ) begin r_mscratch      <= write_if.data; end end

always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mip           <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MIP           ) begin r_mip           <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mbase         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MBASE         ) begin r_mbase         <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mbound        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MBOUND        ) begin r_mbound        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mibase        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MIBASE        ) begin r_mibase        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mibound       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MIBOUND       ) begin r_mibound       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mdbase        <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MDBASE        ) begin r_mdbase        <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mdbound       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MDBOUND       ) begin r_mdbound       <= write_if.data; end end

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_mcycle <= 'h0;
  end else if (write_if.valid & (write_if.addr ==  `SYSREG_ADDR_MCYCLE)) begin
    r_mcycle <= write_if.data;
  end else begin
    r_mcycle <= r_mcycle + 1'b1;
  end
end


logic [$clog2(msrh_conf_pkg::DISP_SIZE): 0] w_inst_bit_cnt;
bit_cnt #(.WIDTH(msrh_conf_pkg::DISP_SIZE)) u_minstret_bit_cnt(.in(i_commit.grp_id & ~i_commit.dead_id), .out(w_inst_bit_cnt));

always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_minstret <= 'h0;
  end else if (write_if.valid & (write_if.addr ==  `SYSREG_ADDR_MINSTRET)) begin
    r_minstret <= write_if.data;
  end else if (i_commit.commit) begin
    /* verilator lint_off WIDTH */
    r_minstret <= r_minstret + w_inst_bit_cnt;
  end
end


always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter3  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER3  ) begin r_mhpmcounter3  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter4  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER4  ) begin r_mhpmcounter4  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter5  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER5  ) begin r_mhpmcounter5  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter6  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER6  ) begin r_mhpmcounter6  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter7  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER7  ) begin r_mhpmcounter7  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter8  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER8  ) begin r_mhpmcounter8  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter9  <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER9  ) begin r_mhpmcounter9  <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter10 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER10 ) begin r_mhpmcounter10 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter11 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER11 ) begin r_mhpmcounter11 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter12 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER12 ) begin r_mhpmcounter12 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter13 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER13 ) begin r_mhpmcounter13 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter14 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER14 ) begin r_mhpmcounter14 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter15 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER15 ) begin r_mhpmcounter15 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter16 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER16 ) begin r_mhpmcounter16 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter17 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER17 ) begin r_mhpmcounter17 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter18 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER18 ) begin r_mhpmcounter18 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter19 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER19 ) begin r_mhpmcounter19 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter20 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER20 ) begin r_mhpmcounter20 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter21 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER21 ) begin r_mhpmcounter21 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter22 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER22 ) begin r_mhpmcounter22 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter23 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER23 ) begin r_mhpmcounter23 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter24 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER24 ) begin r_mhpmcounter24 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter25 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER25 ) begin r_mhpmcounter25 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter26 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER26 ) begin r_mhpmcounter26 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter27 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER27 ) begin r_mhpmcounter27 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter28 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER28 ) begin r_mhpmcounter28 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter29 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER29 ) begin r_mhpmcounter29 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter30 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER30 ) begin r_mhpmcounter30 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpmcounter31 <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPMCOUNTER31 ) begin r_mhpmcounter31 <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent3     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT3     ) begin r_mhpevent3     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent4     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT4     ) begin r_mhpevent4     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent5     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT5     ) begin r_mhpevent5     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent6     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT6     ) begin r_mhpevent6     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent7     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT7     ) begin r_mhpevent7     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent8     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT8     ) begin r_mhpevent8     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent9     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT9     ) begin r_mhpevent9     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent10    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT10    ) begin r_mhpevent10    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent11    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT11    ) begin r_mhpevent11    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent12    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT12    ) begin r_mhpevent12    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent13    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT13    ) begin r_mhpevent13    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent14    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT14    ) begin r_mhpevent14    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent15    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT15    ) begin r_mhpevent15    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent16    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT16    ) begin r_mhpevent16    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent17    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT17    ) begin r_mhpevent17    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent18    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT18    ) begin r_mhpevent18    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent19    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT19    ) begin r_mhpevent19    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent20    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT20    ) begin r_mhpevent20    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent21    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT21    ) begin r_mhpevent21    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent22    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT22    ) begin r_mhpevent22    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent23    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT23    ) begin r_mhpevent23    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent24    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT24    ) begin r_mhpevent24    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent25    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT25    ) begin r_mhpevent25    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent26    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT26    ) begin r_mhpevent26    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent27    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT27    ) begin r_mhpevent27    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent28    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT28    ) begin r_mhpevent28    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent29    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT29    ) begin r_mhpevent29    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent30    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT30    ) begin r_mhpevent30    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_mhpevent31    <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_MHPEVENT31    ) begin r_mhpevent31    <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg0       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPCFG0       ) begin r_pmpcfg0       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg1       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPCFG1       ) begin r_pmpcfg1       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg2       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPCFG2       ) begin r_pmpcfg2       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpcfg3       <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPCFG3       ) begin r_pmpcfg3       <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr0      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR0      ) begin r_pmpaddr0      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr1      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR1      ) begin r_pmpaddr1      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr2      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR2      ) begin r_pmpaddr2      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr3      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR3      ) begin r_pmpaddr3      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr4      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR4      ) begin r_pmpaddr4      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr5      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR5      ) begin r_pmpaddr5      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr6      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR6      ) begin r_pmpaddr6      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr7      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR7      ) begin r_pmpaddr7      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr8      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR8      ) begin r_pmpaddr8      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr9      <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR9      ) begin r_pmpaddr9      <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr10     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR10     ) begin r_pmpaddr10     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr11     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR11     ) begin r_pmpaddr11     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr12     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR12     ) begin r_pmpaddr12     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr13     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR13     ) begin r_pmpaddr13     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr14     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR14     ) begin r_pmpaddr14     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_pmpaddr15     <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_PMPADDR15     ) begin r_pmpaddr15     <= write_if.data; end end
always_ff @ (posedge i_clk, negedge i_reset_n) begin if (!i_reset_n) begin r_stats         <= 'h0; end else if (write_if.valid & write_if.addr ==  `SYSREG_ADDR_STATS         ) begin r_stats         <= write_if.data; end end

assign csr_info.mstatus = w_mstatus;
assign csr_info.mepc    = r_mepc;
assign csr_info.mtvec   = r_mtvec;
assign csr_info.stvec   = r_stvec;
assign csr_info.utvec   = r_utvec;
assign csr_info.sepc    = r_sepc;
assign csr_info.uepc    = r_uepc;
assign csr_info.satp    = r_satp;
// assign csr_info.priv    = r_priv;
// Priviledge should be pass immediately when exception is valid
assign csr_info.priv    = w_priv_next;
assign csr_info.medeleg = r_medeleg;
assign csr_info.sedeleg = r_sedeleg;

logic w_delegate;
assign w_delegate = msrh_conf_pkg::USING_VM & (r_priv <= msrh_pkg::PRV_S) &
                    r_medeleg[int'(i_commit.except_type)];

`define MSTATUS_SIE  1
`define MSTATUS_SPIE 5
`define MSTATUS_SPP  8

`define MSTATUS_MIE  3
`define MSTATUS_MPIE 7
`define MSTATUS_MPP  12:11
`define MSTATUS_FS   14:13
`define MSTATUS_XS   16:15
`define MSTATUS_MPRV 17

`define MSTATUS_SUM 18
`define MSTATUS_MXR 19
`define MSTATUS_TVM 20
`define MSTATUS_TW  21
`define MSTATUS_TSR 22

always_comb begin
  w_mstatus = r_mstatus;
  w_mstatus[riscv_pkg::MSTATUS_SD] = (&w_mstatus[`MSTATUS_FS]) | (&w_mstatus[`MSTATUS_XS]);
end

always_comb begin
  w_mstatus_next = w_mstatus;
  w_priv_next    = r_priv  ;
  w_sepc_next    = r_sepc  ;
  w_scause_next  = r_scause;
  w_stval_next   = r_stval ;
  w_mepc_next    = r_mepc  ;
  w_mcause_next  = r_mcause;
  w_mtval_next   = r_mtval ;

  if (i_commit.commit & |(i_commit.except_valid & ~i_commit.dead_id)) begin
    if (i_commit.except_type == msrh_pkg::MRET) begin
      // r_mepc <= epc;
      /* verilator lint_off WIDTH */
      // r_mcause <= i_commit.except_type;
      // r_mtval <= io.tval;
      w_mstatus_next[`MSTATUS_MPIE] = 1'b1;
      w_mstatus_next[`MSTATUS_MPP ] = msrh_pkg::PRV_U;
      w_mstatus_next[`MSTATUS_MIE ] = w_mstatus[`MSTATUS_MPIE];
      w_priv_next = msrh_pkg::priv_t'(w_mstatus[`MSTATUS_MPP]);
      w_mtval_next = 'h0;
    end else if (i_commit.except_type == msrh_pkg::SRET) begin
      // r_mepc <= epc;
      /* verilator lint_off WIDTH */
      // r_mcause <= i_commit.except_type;
      // r_mtval <= io.tval;
      w_mstatus_next[`MSTATUS_SPIE] = 1'b1;
      w_mstatus_next[`MSTATUS_SPP ] = msrh_pkg::PRV_U;
      w_mstatus_next[`MSTATUS_SIE ] = w_mstatus[`MSTATUS_SPIE];
      w_priv_next = msrh_pkg::priv_t'(w_mstatus[`MSTATUS_SPP]);
      w_mtval_next = 'h0;
    end else if (i_commit.except_type == msrh_pkg::URET) begin // if (i_commit.except_type == msrh_pkg::SRET)
      w_mtval_next = 'h0;
    end else if (w_delegate) begin
      w_sepc_next = i_commit.epc;
      /* verilator lint_off WIDTH */
      w_scause_next = i_commit.except_type;
      if (i_commit.except_type == msrh_pkg::INST_ADDR_MISALIGN  ||
          i_commit.except_type == msrh_pkg::INST_ACC_FAULT      ||
          i_commit.except_type == msrh_pkg::INST_PAGE_FAULT     ||
          i_commit.except_type == msrh_pkg::LOAD_ADDR_MISALIGN  ||
          i_commit.except_type == msrh_pkg::LOAD_ACC_FAULT      ||
          i_commit.except_type == msrh_pkg::LOAD_PAGE_FAULT     ||
          i_commit.except_type == msrh_pkg::STAMO_ADDR_MISALIGN ||
          i_commit.except_type == msrh_pkg::STAMO_ACC_FAULT     ||
          i_commit.except_type == msrh_pkg::STAMO_PAGE_FAULT) begin
        w_stval_next = i_commit.tval;
      end else begin // if (i_commit.except_type == msrh_pkg::INST_ADDR_MISALIGN  ||...
        w_stval_next = 'h0;
      end // if (i_commit.except_type == INST_ADDR_MISALIGN  ||...
      w_mstatus_next[`MSTATUS_SPIE] = w_mstatus[`MSTATUS_SIE];
      w_mstatus_next[`MSTATUS_SPP ] = r_priv[0];
      w_mstatus_next[`MSTATUS_SIE ] = 1'b0;

      w_priv_next = msrh_pkg::PRV_S;
    end else if (i_commit.except_type != msrh_pkg::SILENT_FLUSH &&
                 i_commit.except_type != msrh_pkg::ANOTHER_FLUSH) begin
      w_mepc_next = i_commit.epc;
      /* verilator lint_off WIDTH */
      w_mcause_next = i_commit.except_type;
      if (i_commit.except_type == msrh_pkg::INST_ADDR_MISALIGN  ||
          i_commit.except_type == msrh_pkg::INST_ACC_FAULT      ||
          i_commit.except_type == msrh_pkg::INST_PAGE_FAULT     ||
          i_commit.except_type == msrh_pkg::LOAD_ADDR_MISALIGN  ||
          i_commit.except_type == msrh_pkg::LOAD_ACC_FAULT      ||
          i_commit.except_type == msrh_pkg::LOAD_PAGE_FAULT     ||
          i_commit.except_type == msrh_pkg::STAMO_ADDR_MISALIGN ||
          i_commit.except_type == msrh_pkg::STAMO_ACC_FAULT     ||
          i_commit.except_type == msrh_pkg::STAMO_PAGE_FAULT) begin
        w_mtval_next = i_commit.tval;
      end else begin // if (i_commit.except_type == msrh_pkg::INST_ADDR_MISALIGN  ||...
        w_mtval_next = 'h0;
      end // if (i_commit.except_type == INST_ADDR_MISALIGN  ||...
      w_mstatus_next[`MSTATUS_MPIE] = w_mstatus[`MSTATUS_MIE];
      w_mstatus_next[`MSTATUS_MPP ] = r_priv;
      w_mstatus_next[`MSTATUS_MIE ] = 1'b0;
      w_priv_next = msrh_pkg::PRV_M;
    end // else: !if(w_delegate)
  end else if (write_if.valid) begin
    case(write_if.addr)
      `SYSREG_ADDR_SEPC : begin
        w_sepc_next = write_if.data;
      end
      `SYSREG_ADDR_SCAUSE : begin
        w_scause_next = write_if.data;
      end
      `SYSREG_ADDR_STVAL : begin
        w_stval_next      = write_if.data;
      end
      `SYSREG_ADDR_MEPC : begin
        w_mepc_next       = write_if.data;
      end
      `SYSREG_ADDR_MCAUSE : begin
        w_mcause_next     = write_if.data;
      end
      `SYSREG_ADDR_MTVAL : begin
        w_mtval_next      = write_if.data;
      end
      `SYSREG_ADDR_MSTATUS : begin
        // r_mstatus <= write_if.data;
        w_mstatus_next[`MSTATUS_MIE ] = write_if.data[`MSTATUS_MIE ];
        w_mstatus_next[`MSTATUS_MPIE] = write_if.data[`MSTATUS_MPIE];

        w_mstatus_next[`MSTATUS_MPRV] = write_if.data[`MSTATUS_MPRV];
        w_mstatus_next[`MSTATUS_MPP ] = write_if.data[`MSTATUS_MPP];

        w_mstatus_next[`MSTATUS_SPP ] = write_if.data[`MSTATUS_SPP ];
        w_mstatus_next[`MSTATUS_SPIE] = write_if.data[`MSTATUS_SPIE];
        w_mstatus_next[`MSTATUS_SIE ] = write_if.data[`MSTATUS_SIE ];
        w_mstatus_next[`MSTATUS_TW  ] = write_if.data[`MSTATUS_TW  ];
        w_mstatus_next[`MSTATUS_TSR ] = write_if.data[`MSTATUS_TSR ];

        if (msrh_conf_pkg::USING_VM) begin
          w_mstatus_next[`MSTATUS_MXR] = write_if.data[`MSTATUS_MXR];
          w_mstatus_next[`MSTATUS_SUM] = write_if.data[`MSTATUS_SUM];
          w_mstatus_next[`MSTATUS_TVM] = write_if.data[`MSTATUS_TVM];
        end

        w_mstatus_next[`MSTATUS_FS] = write_if.data[`MSTATUS_FS];
      end // case: `SYSREG_ADDR_MSTATUS

      `SYSREG_ADDR_SSTATUS : begin
        w_mstatus_next[`MSTATUS_SIE ] = write_if.data[`MSTATUS_SIE ];
        w_mstatus_next[`MSTATUS_SPIE] = write_if.data[`MSTATUS_SPIE];
        w_mstatus_next[`MSTATUS_SPP ] = write_if.data[`MSTATUS_SPP ];
        w_mstatus_next[`MSTATUS_XS  ] = write_if.data[`MSTATUS_XS  ];
        w_mstatus_next[`MSTATUS_FS  ] = write_if.data[`MSTATUS_FS  ];
        w_mstatus_next[`MSTATUS_MPP ] = write_if.data[`MSTATUS_MPP ];
        w_mstatus_next[`MSTATUS_MXR ] = write_if.data[`MSTATUS_MXR ];
        w_mstatus_next[`MSTATUS_SUM ] = write_if.data[`MSTATUS_SUM ];
      end
      default : begin end
    endcase // case (write_if.addr)
  end // if (write_if.valid)
end // always_comb


always_ff @ (posedge i_clk, negedge i_reset_n) begin
  if (!i_reset_n) begin
    r_priv <= msrh_pkg::PRV_M;
    r_mstatus <= riscv_pkg::init_mstatus;

    r_sepc <= 'h0;
    r_scause <= 'h0;
    r_stval <= 'h0;

    r_mepc <= 'h0;
    r_mcause <= 'h0;
    r_mtval <= 'h0;
  end else begin
    r_priv <= w_priv_next;
    r_mstatus <= w_mstatus_next;

    r_sepc   <= w_sepc_next  ;
    r_scause <= w_scause_next;
    r_stval  <= w_stval_next ;

    r_mepc   <= w_mepc_next  ;
    r_mcause <= w_mcause_next;
    r_mtval  <= w_mtval_next ;
  end // else: !if(!i_reset_n)

end // always_ff @ (posedge i_clk, negedge i_reset_n)


endmodule // msrh_csr
