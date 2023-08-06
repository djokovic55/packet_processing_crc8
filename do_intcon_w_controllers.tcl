
clear -all

# verif
analyze -sv09 checker_axi.sv checker_master_axi_cont.sv top_tb.sv

# src
analyze -vhdl top.vhd interconnect.vhd arbiter_rr.vhd controller.vhd external_regs.vhd incomming_data_memory.vhd  int_fsm.vhd master_axi_cont.vhd outgoing_data_memory.vhd packet_builder1.vhd packet_builder2.vhd packet_parser.vhd regs.vhd slave_axi_cont.vhd 

elaborate -vhdl -top {top}

clock clk
reset reset

prove -bg -all



















