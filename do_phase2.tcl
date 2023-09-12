
clear -all

# verif
analyze -sv09 checker_top_ex_regs.sv checker_regs.sv bind_phase2.sv

# src
analyze -vhdl top.vhd interconnect.vhd arbiter_rr.vhd controller.vhd external_regs.vhd incomming_data_memory.vhd  int_fsm.vhd master_axi_cont.vhd outgoing_data_memory.vhd packet_builder.vhd packet_parser.vhd regs.vhd slave_axi_cont.vhd 
analyze -vhdl slave_axi_lite_ex_regs_cont.vhd slave_axi_lite_regs_cont.vhd

elaborate -vhdl -top {top}

clock clk
reset reset

prove -bg -all
