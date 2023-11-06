
clear -all

# verif
analyze -sv09 checker_pb.sv checker_axi.sv checker_data_integrity.sv bind_pb.sv

# src
analyze -vhdl master_axi_cont.vhd packet_builder.vhd 
analyze -vhdl fifo.vhd crc_top.vhd crc8_parallel.vhd hamming_12_8.vhd 

elaborate -vhdl -top {packet_builder}

clock m_axi_aclk
reset m_axi_aresetn

# visualize -confirm -vcd unstable_data_wlast_bugs.vcd -window visualize:0
prove -bg -all
