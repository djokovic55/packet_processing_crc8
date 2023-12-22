
clear -all
# verif

analyze -sv09 checker_top.sv bind_top.sv checker_data_integrity.sv checker_axi.sv checker_fair_int.sv

# src
analyze -vhdl top.vhd top_subsystem.vhd interconnect.vhd arbiter_rr.vhd int_fsm.vhd controller.vhd external_regs.vhd data_memory.vhd master_axi_cont.vhd packet_builder.vhd packet_parser.vhd 
analyze -vhdl regs.vhd slave_axi_cont.vhd 
analyze -vhdl slave_axi_lite_ex_regs_cont.vhd slave_axi_lite_regs_cont.vhd bram.vhd fifo.vhd crc_top.vhd crc8_parallel.vhd hamming_12_8.vhd hamming_check.vhd


check_fsv -init
elaborate -vhdl -top {top}
clock clk
reset reset

# FSV COMMANDS
# check_fsv -fault -add subsys.parser.axi_read_data_s(4) -type SA1 -silent
# ADD FAULTS
check_fsv -fault -add outmem.slave_axi_cont_inmem.axi_rdata(4) -type SA1 -silent
# ADD STROBES
# check_fsv -strobe -add outmem.S_AXI_RDATA -functional
check_fsv -strobe -add subsys.parser.header_reg -functional
check_fsv -strobe -add subsys.parser.hamming_parity_check_out_s -checker -checker_mode diff
set_fsv_generate_detectability On; set_fsv_clock_cycle_time 0
set_fsv_generate_always_propagated On; set_fsv_generate_always_detected On; set_fsv_clock_cycle_time 0
check_fsv -structural
check_fsv -generate
check_fsv -prove

## Use the existing trace as initial value for another formal proof.
#prove -from <embedded>::top.chk_top.cov_no_ecc_uncorr_err -task . -bg

# CREATING TASKS COMMANDS
#
# create regs_verif task
# task -create regs_verif -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy <embedded>::top.chk_top.ast_pb0_addr_in <embedded>::top.chk_top.ast_pb0_addr_in:precondition1 <embedded>::top.chk_top.ast_pb0_byte_cnt <embedded>::top.chk_top.ast_pb0_byte_cnt:precondition1 <embedded>::top.chk_top.ast_pb0_pkt_type <embedded>::top.chk_top.ast_pb0_pkt_type:precondition1 <embedded>::top.chk_top.ast_pb0_ecc_en <embedded>::top.chk_top.ast_pb0_ecc_en:precondition1 <embedded>::top.chk_top.ast_pb0_crc_en <embedded>::top.chk_top.ast_pb0_crc_en:precondition1 <embedded>::top.chk_top.ast_pb0_ins_ecc_err <embedded>::top.chk_top.ast_pb0_ins_ecc_err:precondition1 <embedded>::top.chk_top.ast_pb0_ins_crc_err <embedded>::top.chk_top.ast_pb0_ins_crc_err:precondition1 <embedded>::top.chk_top.ast_pb0_ecc_val <embedded>::top.chk_top.ast_pb0_ecc_val:precondition1 <embedded>::top.chk_top.ast_pb0_crc_val <embedded>::top.chk_top.ast_pb0_crc_val:precondition1 <embedded>::top.chk_top.ast_pb0_sop_val <embedded>::top.chk_top.ast_pb0_sop_val:precondition1 <embedded>::top.chk_top.ast_pb0_data_sel <embedded>::top.chk_top.ast_pb0_data_sel:precondition1 <embedded>::top.chk_top.ast_pb0_addr_out <embedded>::top.chk_top.ast_pb0_addr_out:precondition1
# prove it using engine M
# prove -task regs_verif -engine_mode {M} -bg

# create data_integrity task
# task -create data_integrity -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy <embedded>::top.subsys.chk_data_integrity.ast_packet_integrity <embedded>::top.subsys.chk_data_integrity.ast_packet_integrity:precondition1
# prove it using engine N
# prove -task  data_integrity -engine_mode {N} -bg

# create intcon_fairness task
# task -create intcon_fairness -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy <embedded>::top.subsys.intcon.arb_inst.chk_fairness.ast_fairness <embedded>::top.subsys.intcon.arb_inst.chk_fairness.ast_fairness:precondition1 <embedded>::top.subsys.intcon.arb_inst.chk_fairness.ast_no_deadlock
# prove it using engine M
# prove -task  intcon_fairness -engine_mode {B,M} -bg

# create axi_prot task
# task -create axi_prot -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy <embedded>::top.subsys.intcon.chk_axi_prot.ast_aw_stable_awaddr <embedded>::top.subsys.intcon.chk_axi_prot.ast_aw_stable_awaddr:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_aw_stable_awlen <embedded>::top.subsys.intcon.chk_axi_prot.ast_aw_stable_awlen:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_aw_stable_awsize <embedded>::top.subsys.intcon.chk_axi_prot.ast_aw_stable_awsize:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_aw_stable_awburst <embedded>::top.subsys.intcon.chk_axi_prot.ast_aw_stable_awburst:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_aw_awvalid_until_awready <embedded>::top.subsys.intcon.chk_axi_prot.ast_aw_awvalid_until_awready:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_w_stable_wdata <embedded>::top.subsys.intcon.chk_axi_prot.ast_w_stable_wdata:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_w_stable_wstrb <embedded>::top.subsys.intcon.chk_axi_prot.ast_w_stable_wstrb:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_w_data_wlast <embedded>::top.subsys.intcon.chk_axi_prot.ast_w_data_wlast:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_w_wvalid_until_wready <embedded>::top.subsys.intcon.chk_axi_prot.ast_w_wvalid_until_wready:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_ar_stable_araddr <embedded>::top.subsys.intcon.chk_axi_prot.ast_ar_stable_araddr:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_ar_stable_arlen <embedded>::top.subsys.intcon.chk_axi_prot.ast_ar_stable_arlen:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_ar_stable_arsize <embedded>::top.subsys.intcon.chk_axi_prot.ast_ar_stable_arsize:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_ar_stable_arburst <embedded>::top.subsys.intcon.chk_axi_prot.ast_ar_stable_arburst:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_ar_arvalid_until_arready <embedded>::top.subsys.intcon.chk_axi_prot.ast_ar_arvalid_until_arready:precondition1 <embedded>::top.subsys.intcon.chk_axi_prot.ast_r_data_rlast <embedded>::top.subsys.intcon.chk_axi_prot.ast_r_data_rlast:precondition1
# prove it using engine N
# prove -task  axi_prot -engine_mode {N} -bg

# create pp_end task
# task -create pp_end -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy <embedded>::top.chk_top.cov_pp_end
# prove -bg -all

#task -create data_integrity -set -source_task <embedded> -copy_stopats -copy_abstractions all -copy_assumes -copy <embedded>::top.subsys.chk_data_integrity.ast_packet_integrity <embedded>::top.subsys.chk_data_integrity.ast_packet_integrity:precondition1


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
