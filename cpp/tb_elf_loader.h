#pragma once

#include "basic.hpp"

extern "C" {
  extern Addr_t  tohost_addr;
  extern bool    tohost_en;
}

extern "C" int load_binary(
    char const* path_exec,
    char const* filename,
    bool is_load_dump);
