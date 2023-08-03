
clear -all

analyze -sv09 checker_axi.sv checker_master_axi_cont.sv bind_intcon_w_controllers.sv
# analyze -vhdl interconnect.vhd int_fsm.vhd arbiter_rr.vhd master_axi_cont.vhd
analyze -vhdl *.vhd

elaborate -vhdl -top top

clock clk
reset reset

prove -bg -all