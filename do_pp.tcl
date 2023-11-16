
clear -all

# verif
analyze -sv09 checker_pp.sv checker_axi.sv bind_pp.sv

# src
analyze -vhdl master_axi_cont.vhd packet_parser.vhd 
analyze -vhdl fifo.vhd crc_top.vhd crc8_parallel.vhd hamming_12_8.vhd hamming_check.vhd 

elaborate -vhdl -top {packet_parser}

clock m_axi_aclk
reset m_axi_aresetn

# visualize -confirm -vcd unstable_data_wlast_bugs.vcd -window visualize:0
visualize -property <embedded>::packet_parser.chk_pp.cov_pp_start -new_window
visualize -min_length [expr [visualize -get_length -window visualize:0] + 30] -window visualize:0; visualize -freeze [visualize -get_length -window visualize:0] -window visualize:0; visualize -replot -bg -window visualize:0

prove -bg -all
