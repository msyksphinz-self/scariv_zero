set WildcardFilter [lsearch -not -all -inline $WildcardFilter Memory]
add wave * -recursive
run -all
archive write vsim.dbar -wlf vsim.wlf
quit
