
clear -all

# verif
analyze -sv09 checker_top_ex_regs.sv checker_regs.sv checker_axi_slave.sv bind_phase2.sv

# src
analyze -vhdl top.vhd interconnect.vhd arbiter_rr.vhd controller.vhd external_regs.vhd data_memory.vhd  int_fsm.vhd master_axi_cont.vhd packet_builder.vhd packet_parser.vhd regs.vhd slave_axi_cont.vhd 
analyze -vhdl slave_axi_lite_ex_regs_cont.vhd slave_axi_lite_regs_cont.vhd bram.vhd fifo.vhd crc_top.vhd crc8_parallel.vhd hamming_12_8.vhd hamming_check.vhd

elaborate -vhdl -top {top}

clock clk
reset reset

prove -bg -all



# COMPLEXITY MANAGER COMMANDS
#  
# Create new task and copy properties from source task
# task -create <pb0_op0_start> -set -source_task <embedded> -copy <embedded>::top.system_regs.chk_regs.pb0_start_c
# task -create <pb0_op0_start_flop_gates_cmt> -copy_all -set
#
# List arrays which could be potenital cutpoints
# get_design_info -property <pb0_op0_start>::top.system_regs.chk_regs.pb0_start_c -list array
#
# Add cutpoint (stopat) for each md array in a design
# foreach a [get_design_info -list array -silent] { stopat $a}
# 
# Add cupoint on pb1 block
# stopat top.packet_builder0.*
#
# Create new task and copy all undetermined props
# task -create <undet> -source_task <embedded> -copy [get_property_list -include {type cover status undetermined} -task <embedded>]
# 
# Edit new task with apstractions and cutpoints from other task
# task -edit <undet> -source_task <pb0_op0_start_flop_gates> -copy_stopats -copy_abstractions all -copy_assumes
# 
# Prove task with additional settings
# prove -task <undet> -engine_mode {B N I} -per_property_time_limit 5m -per_property_time_limit_factor 0 -bg
#
