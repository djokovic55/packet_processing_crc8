
clear -all

# verif
analyze -sv09 checker_axi.sv checker_master.sv checker_fair_int.sv bind_int.sv

# src
analyze -vhdl interconnect.vhd arbiter_rr.vhd int_fsm.vhd master_axi_cont.vhd slave_axi_cont.vhd 

elaborate -vhdl -top {interconnect}

clock clk
reset reset

prove -bg -all



















