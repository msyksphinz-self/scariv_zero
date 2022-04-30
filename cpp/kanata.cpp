#include <map>
#include "disasm.h"
#include "kanata.h"

FILE *kanata_fp = NULL;
disassembler_t *disasm;

void init_kanata ()
{
  if ((kanata_fp = fopen("kanata.log", "w")) == NULL) {
    perror("failed to open log file");
    exit(EXIT_FAILURE);
  }
  fprintf(kanata_fp, "Kanata 0004\n");
  disasm = new disassembler_t (64);
}

void start_kanata (long long cycle)
{
  fprintf (kanata_fp, "C=   %d\n", cycle);
}

void proceed_kanata_cycle(int cycle)
{
  fprintf (kanata_fp, "C   %d\n", cycle);
}


void log_dispatch(long long id, long long pc, int inst)
{
  fprintf (kanata_fp, "L %l 0 %08x:%s\n",
           id, pc,
           disasm->disassemble(inst).c_str());
}


std::map<long long, const char *> stage_map;

void log_stage (long long id, char *stage)
{
  decltype(stage_map)::iterator it = stage_map.find(id);
  if (it != stage_map.end()) {
    stage_map.erase (id);
    fprintf (kanata_fp, "E %l 0 %s\n", id, it->second);
  }
  fprintf (kanata_fp, "S %l 0 %s\n", id, stage);
  stage_map.insert (std::make_pair(id, stage));
}
