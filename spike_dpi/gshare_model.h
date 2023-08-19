#pragma once
#include <svdpi.h>

extern "C" {

  void initial_gshare(long long bhr_length,
                      long long cache_block_byte_size);
  void step_gshare (long long rtl_time,
                    int rtl_cmt_id, int rtl_grp_id,
                    long long rtl_gshare_bhr);
}
