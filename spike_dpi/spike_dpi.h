#pragma once

extern "C" {
  void initial_spike (const char *filename);
  void step_spike(long long time, long long rtl_pc,
                  int rtl_cmt_id, int rtl_grp_id,
                  int rtl_insn,
                  int rtl_wr_valid, int rtl_wr_gpr_addr,
                  long long rtl_wr_val);
}
