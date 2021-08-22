#----------------------------------------------------------
# Proc
#----------------------------------------------------------

set dump $env(DUMP_TYPE)

proc dump_vcd {start length hier} {
  run $start ns
  open_vcd out.vcd
  log_vcd -level 0 $hier
  if {$length == 0} {
    run all
  } else {
    run $length ns
    close_vcd
    run all
  }
  quit
}

proc dump_wdb {start length hier} {
  log_wave -r $hier
  run all
  quit
}

#----------------------------------------------------------
# Main
#----------------------------------------------------------

# if { [string match "on" $gui ] } {
#   start_gui
# } else {
switch $dump {
    "vcd"   { dump_vcd 0 0 / }
    "wdb"   { dump_wdb 0 0 / }
    "off"   { run -all; quit }
    default { puts "DUMP=$dump is not supported"; quit }
}
# }
