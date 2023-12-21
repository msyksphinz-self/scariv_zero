#pragma once
#include <svdpi.h>

extern "C" {
  void initial_gshare(long long bhr_length,
                      long long bht_length,
                      long long cache_block_byte_size);
  void step_gshare (long long rtl_commit_time,
                    long long rtl_f2_time,
                    long long rtl_disp_time,
                    int rtl_cmt_id, int rtl_grp_id, int rtl_brtag,
                    long long rtl_gshare_bhr,
                    int rtl_gshare_rd_bht_index,
                    int rtl_gshare_wr_bht_index,
                    int rtl_taken,
                    int rtl_predict_taken,
                    int rtl_mispredict);
}
