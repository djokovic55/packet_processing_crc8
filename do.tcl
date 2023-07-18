clear -all

analyze -sv09 checker_int.sv bind.sv
analyze -vhdl interconnect.vhd int_fsm.vhd arbiter_rr.vhd 

elaborate -vhdl -top interconnect

clock clk
reset reset

prove -bg -all
