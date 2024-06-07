
clear -all

################################################################################
# Init coverage app 
################################################################################
check_cov -init
set_prove_time_limit 0s
# check_cov -init -type {proof bound} -model all -exclude_instance { * } -include_instance {subsys.chk_data_integrity} 
# check_cov -init -type {bound}
################################################################################

################################################################################
# Init fsv app 
################################################################################
# check_fsv -init
################################################################################

# set_proof_structure_support_embedded_on_case_split on

################################################################################
# Elaboration
################################################################################

# verif
analyze -sv09 {checker_top.sv bind_top.sv checker_data_integrity.sv checker_axi.sv checker_fair_int.sv crc_chk_calc.sv checker_di_top.sv}

# src
analyze -vhdl top.vhd top_subsystem.vhd interconnect.vhd arbiter_rr.vhd int_fsm.vhd controller.vhd external_regs.vhd data_memory.vhd master_axi_cont.vhd packet_builder.vhd packet_parser.vhd 
analyze -vhdl regs.vhd slave_axi_cont.vhd 
analyze -vhdl slave_axi_lite_ex_regs_cont.vhd slave_axi_lite_regs_cont.vhd bram.vhd fifo.vhd crc_top.vhd crc8_parallel.vhd hamming_12_8.vhd hamming_check.vhd

elaborate -vhdl -top {top}
clock clk
reset reset

################################################################################
# Apstraction variables
################################################################################

set csa 0
set iva 0
set inmem_iva 0

################################################################################
# Apstraction - PB1 always busy
################################################################################
# stopat subsys.system_regs.pb1_sts_s
# assume -name pb1_always_busy -env {subsys.system_regs.pb1_sts_s = '0'}

# First create task and then add abstractions and stopats
################################################################################
# TASKs
## Create crc debug task
# task -create crc_debug -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy <embedded>::top.chk_top.ast_crc_err <embedded>::top.chk_top.ast_crc_err:precondition1 <embedded>::top.chk_top.ast_crc_no_err <embedded>::top.chk_top.ast_crc_no_err:precondition1 <embedded>::top.chk_top.ast_crc_err_when_ecc_err_exists <embedded>::top.chk_top.ast_crc_err_when_ecc_err_exists:precondition1 <embedded>::top.chk_top.ast_crc_no_err_when_ecc_err_exists <embedded>::top.chk_top.ast_crc_no_err_when_ecc_err_exists:precondition1
################################################################################
if {$csa == 1} {

  ## Create csa debug task
	task -create csa_debug -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
	<embedded>::top.chk_top.cov_pp_pb0_work 
	<embedded>::top.chk_top.cov_pp_pb1_work  
	<embedded>::top.chk_top.cov_pb0_pb1_work 
	<embedded>::top.chk_top.cov_pb0_pb1_long_work 
	<embedded>::top.chk_top.cov_pb0_work 

	<embedded>::top.chk_top.cov_pb0_check
	<embedded>::top.chk_top.cov_pb1_check
	<embedded>::top.chk_top.cov_2pb0
	<embedded>::top.chk_top.cov_2pb1
	<embedded>::top.chk_top.cov_2pp

	<embedded>::top.chk_top.pb0_di.cov_no_zero_data
	<embedded>::top.chk_top.pb1_di.cov_no_zero_data

	<embedded>::top.chk_top.ast_pb0_di 
	<embedded>::top.chk_top.ast_pb1_di 
	<embedded>::top.chk_top.ast_crc_pb0_di
	<embedded>::top.chk_top.ast_crc_pb1_di
	<embedded>::top.chk_top.ast_pp_ecc_corr_err
	<embedded>::top.chk_top.ast_pp_ecc_uncorr_err
	}

################################################################################
# Apstraction -  Stopats for Internal Registers 
# It is important to have the same configuration on top and in registers 
# in order to have coherent data in both checker and rtl
################################################################################
# PB0 task
################################################################################
# Start register
	stopat subsys.system_regs.pb0_ctrl0_s
# if pb0 is active, start should remain low because is serves as a reset signal for some registers
	assume -name asm_stopat_top_pb0_start {chk_top.pb0_busy_top = 0 |->  subsys.system_regs.pb0_ctrl0_s = 0}
# Addr_in register
	stopat subsys.system_regs.pb0_ctrl2_s
	assume -name asm_stopat_top_pb0_addr_in {subsys.system_regs.pb0_ctrl2_s = chk_top.pb_addr_in}

# Config register
	stopat subsys.system_regs.pb0_ctrl3_s

	assume -name asm_stopat_top_pb0_byte_cnt {subsys.system_regs.pb0_ctrl3_s(3 downto 0) = chk_top.pb_byte_cnt}
	assume -name asm_stopat_top_pb0_pkt_type {subsys.system_regs.pb0_ctrl3_s(7 downto 4) = chk_top.pb_pkt_type}
	assume -name asm_stopat_top_pb0_ecc_en {subsys.system_regs.pb0_ctrl3_s(8) = chk_top.pb_ecc_en}
	assume -name asm_stopat_top_pb0_crc_en {subsys.system_regs.pb0_ctrl3_s(9) = chk_top.pb_crc_en}
	assume -name asm_stopat_top_pb0_ins_ecc_err {subsys.system_regs.pb0_ctrl3_s(11 downto 10) = chk_top.pb_ins_ecc_err}
	assume -name asm_stopat_top_pb0_ins_crc_err {subsys.system_regs.pb0_ctrl3_s(12) = chk_top.pb_ins_crc_err}
	assume -name asm_stopat_top_pb0_ecc_val {subsys.system_regs.pb0_ctrl3_s(16 downto 13) = chk_top.pb_ecc_val}
	assume -name asm_stopat_top_pb0_crc_val {subsys.system_regs.pb0_ctrl3_s(24 downto 17) = chk_top.pb_crc_val}
	assume -name asm_stopat_top_pb0_sop_val {subsys.system_regs.pb0_ctrl3_s(27 downto 25) = chk_top.pb_sop_val}
	assume -name asm_stopat_top_pb0_data_sel {subsys.system_regs.pb0_ctrl3_s(31 downto 28) = chk_top.pb_data_sel}

# Addr_out register
	stopat subsys.system_regs.pb0_ctrl4_s
	assume -name asm_stopat_top_pb0_addr_out {subsys.system_regs.pb0_ctrl4_s = chk_top.pb_addr_out}

################################################################################
# PB1 task
################################################################################
#
# Start register
	stopat subsys.system_regs.pb1_ctrl0_s
	assume -name asm_stopat_top_pb1_start {chk_top.pb1_busy_top = 0 |->  subsys.system_regs.pb1_ctrl0_s = 0}
# Addr_in register
	stopat subsys.system_regs.pb1_ctrl2_s
	assume -name asm_stopat_top_pb1_addr_in {subsys.system_regs.pb1_ctrl2_s = chk_top.pb_addr_in}

# Config register
	stopat subsys.system_regs.pb1_ctrl3_s
	assume -name asm_stopat_top_pb1_byte_cnt {subsys.system_regs.pb1_ctrl3_s(3 downto 0) = chk_top.pb_byte_cnt}
	assume -name asm_stopat_top_pb1_pkt_type {subsys.system_regs.pb1_ctrl3_s(7 downto 4) = chk_top.pb_pkt_type}
	assume -name asm_stopat_top_pb1_ecc_en {subsys.system_regs.pb1_ctrl3_s(8) = chk_top.pb_ecc_en}
	assume -name asm_stopat_top_pb1_crc_en {subsys.system_regs.pb1_ctrl3_s(9) = chk_top.pb_crc_en}
	assume -name asm_stopat_top_pb1_ins_ecc_err {subsys.system_regs.pb1_ctrl3_s(11 downto 10) = chk_top.pb_ins_ecc_err}
	assume -name asm_stopat_top_pb1_ins_crc_err {subsys.system_regs.pb1_ctrl3_s(12) = chk_top.pb_ins_crc_err}
	assume -name asm_stopat_top_pb1_ecc_val {subsys.system_regs.pb1_ctrl3_s(16 downto 13) = chk_top.pb_ecc_val}
	assume -name asm_stopat_top_pb1_crc_val {subsys.system_regs.pb1_ctrl3_s(24 downto 17) = chk_top.pb_crc_val}
	assume -name asm_stopat_top_pb1_sop_val {subsys.system_regs.pb1_ctrl3_s(27 downto 25) = chk_top.pb_sop_val}
	assume -name asm_stopat_top_pb1_data_sel {subsys.system_regs.pb1_ctrl3_s(31 downto 28) = chk_top.pb_data_sel}

# Addr_out register
	stopat subsys.system_regs.pb1_ctrl4_s
	assume -name asm_stopat_top_pb1_addr_out {subsys.system_regs.pb1_ctrl4_s = chk_top.pb_addr_out}
################################################################################

################################################################################
# PP task
################################################################################
# Start register
	stopat subsys.system_regs.pp_ctrl0_s
	assume -name asm_stopat_top_pp_start {chk_top.pp_busy_top = 0 |->  subsys.system_regs.pp_ctrl0_s = 0}
# Addr_hdr register
	stopat subsys.system_regs.pp_ctrl2_s
	assume -name asm_stopat_top_pp_addr_hdr {subsys.system_regs.pp_ctrl2_s = chk_top.pp_addr_hdr}

# Ignore ecc errs register
	stopat subsys.system_regs.pp_ctrl3_s
	assume -name asm_stopat_pp_ignore_ecc_err {subsys.system_regs.pp_ctrl3_s = chk_top.pp_ignore_ecc_err}
} 
if {$iva == 1} {
  ## Create iva debug task
	task -create iva_debug -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy * 
#	{
#	<embedded>::top.chk_top.cov_pp_pb0_work 
#	<embedded>::top.chk_top.cov_pp_pb1_work  
#	<embedded>::top.chk_top.cov_pb0_pb1_work 
#	<embedded>::top.chk_top.cov_pb0_pb1_long_work 
#	<embedded>::top.chk_top.cov_pb0_work 
#
#	<embedded>::top.chk_top.cov_pb0_check
#	<embedded>::top.chk_top.cov_pb1_check
#	<embedded>::top.chk_top.cov_2pb0
#	<embedded>::top.chk_top.cov_2pb1
#	<embedded>::top.chk_top.cov_2pp
#
#	<embedded>::top.chk_top.pb0_di.cov_no_zero_data
#	<embedded>::top.chk_top.pb1_di.cov_no_zero_data
#
#	<embedded>::top.chk_top.ast_pb0_di 
#	<embedded>::top.chk_top.ast_pb1_di 
#	<embedded>::top.chk_top.ast_crc_pb0_di
#	<embedded>::top.chk_top.ast_crc_pb1_di
#	<embedded>::top.chk_top.ast_ecc_corr_err
#	<embedded>::top.chk_top.ast_ecc_uncorr_err
#	}

################################################################################
# Apstraction - IVAs for Internal Registers 
################################################################################
# PB0 task
################################################################################
# Start register
	abstract -init_value subsys.system_regs.pb0_ctrl0_s
# Addr_in register
	abstract -init_value subsys.system_regs.pb0_ctrl2_s
	assume -bound 1 -name asm_iva_pb0_addr_in {subsys.system_regs.pb0_ctrl2_s < x"13"}
	assume -bound 1 -name asm_iva_top_pb0_addr_in {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl2_s = chk_top.pb_addr_in}

# Config register
	abstract -init_value subsys.system_regs.pb0_ctrl3_s
	assume -bound 1 -name asm_iva_pb0_data_sel {subsys.system_regs.pb0_ctrl3_s(31 downto 28) < x"3" }

	assume -bound 1 -name asm_iva_top_pb0_byte_cnt {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(3 downto 0) = chk_top.pb_byte_cnt}
	assume -bound 1 -name asm_iva_top_pb0_pkt_type {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(7 downto 4) = chk_top.pb_pkt_type}
	assume -bound 1 -name asm_iva_top_pb0_ecc_en {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(8) = chk_top.pb_ecc_en}
	assume -bound 1 -name asm_iva_top_pb0_crc_en {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(9) = chk_top.pb_crc_en}
	assume -bound 1 -name asm_iva_top_pb0_ins_ecc_err {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(11 downto 10) = chk_top.pb_ins_ecc_err}
	assume -bound 1 -name asm_iva_top_pb0_ins_crc_err {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(12) = chk_top.pb_ins_crc_err}
	assume -bound 1 -name asm_iva_top_pb0_ecc_val {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(16 downto 13) = chk_top.pb_ecc_val}
	assume -bound 1 -name asm_iva_top_pb0_crc_val {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(24 downto 17) = chk_top.pb_crc_val}
	assume -bound 1 -name asm_iva_top_pb0_sop_val {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(27 downto 25) = chk_top.pb_sop_val}
	assume -bound 1 -name asm_iva_top_pb0_data_sel {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(31 downto 28) = chk_top.pb_data_sel}

# Addr_out register
	abstract -init_value subsys.system_regs.pb0_ctrl4_s
	assume -bound 1 -name asm_iva_pb0_addr_out {subsys.system_regs.pb0_ctrl4_s < x"13"}
	assume -bound 1 -name asm_iva_top_pb0_addr_out {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl4_s = chk_top.pb_addr_out}

################################################################################
# PB1 task
################################################################################
# Start register
	abstract -init_value subsys.system_regs.pb1_ctrl0_s
# Addr_in register
	abstract -init_value subsys.system_regs.pb1_ctrl2_s
	assume -bound 1 -name asm_iva_pb1_addr_in {subsys.system_regs.pb1_ctrl2_s < x"13"}
	assume -bound 1 -name asm_iva_top_pb1_addr_in {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl2_s = chk_top.pb_addr_in}

# Config register
	abstract -init_value subsys.system_regs.pb1_ctrl3_s
	assume -bound 1 -name asm_iva_pb1_data_sel {subsys.system_regs.pb1_ctrl3_s(31 downto 28) < x"3" }
	assume -bound 1 -name asm_iva_top_pb1_byte_cnt {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(3 downto 0) = chk_top.pb_byte_cnt}
	assume -bound 1 -name asm_iva_top_pb1_pkt_type {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(7 downto 4) = chk_top.pb_pkt_type}
	assume -bound 1 -name asm_iva_top_pb1_ecc_en {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(8) = chk_top.pb_ecc_en}
	assume -bound 1 -name asm_iva_top_pb1_crc_en {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(9) = chk_top.pb_crc_en}
	assume -bound 1 -name asm_iva_top_pb1_ins_ecc_err {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(11 downto 10) = chk_top.pb_ins_ecc_err}
	assume -bound 1 -name asm_iva_top_pb1_ins_crc_err {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(12) = chk_top.pb_ins_crc_err}
	assume -bound 1 -name asm_iva_top_pb1_ecc_val {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(16 downto 13) = chk_top.pb_ecc_val}
	assume -bound 1 -name asm_iva_top_pb1_crc_val {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(24 downto 17) = chk_top.pb_crc_val}
	assume -bound 1 -name asm_iva_top_pb1_sop_val {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(27 downto 25) = chk_top.pb_sop_val}
	assume -bound 1 -name asm_iva_top_pb1_data_sel {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(31 downto 28) = chk_top.pb_data_sel}

# Addr_out register
	abstract -init_value subsys.system_regs.pb1_ctrl4_s
	assume -bound 1 -name asm_iva_pb1_addr_out {subsys.system_regs.pb1_ctrl4_s < x"13"}
	assume -bound 1 -name asm_iva_top_pb1_addr_out {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl4_s = chk_top.pb_addr_out}
################################################################################

################################################################################
# PP task
################################################################################
# Start register
	abstract -init_value subsys.system_regs.pp_ctrl0_s
# Addr_hdr register
	abstract -init_value subsys.system_regs.pp_ctrl2_s
	assume -bound 1 -name asm_iva_pp_addr_hdr {subsys.system_regs.pp_ctrl2_s < x"13"}
	assume -bound 1 -name asm_iva_top_pp_addr_hdr {subsys.system_regs.pp_ctrl2_s = chk_top.pp_addr_hdr}

# Ignore ecc errs register
	abstract -init_value subsys.system_regs.pp_ctrl3_s
	assume -bound 1 -name asm_iva_pp_ignore_ecc_err {subsys.system_regs.pp_ctrl3_s = chk_top.pp_ignore_ecc_err}
}

################################################################################
# INMEM 
################################################################################
if {$inmem_iva == 1} {
	task -set csa_debug
	abstract -init_value inmem.inmem_bram.ram_s
	for {set i 0} {$i < 19} {incr i} {
		assume -name asm_inmem_loc${i}_val "chk_top.pb0_checker_en = 1 |-> 
			inmem.inmem_bram.ram_s($i) = 0 or 
			inmem.inmem_bram.ram_s($i) = 2 or 
			inmem.inmem_bram.ram_s($i) = 4 or 
			inmem.inmem_bram.ram_s($i) = 8 or 
			inmem.inmem_bram.ram_s($i) = 16 or 
			inmem.inmem_bram.ram_s($i) = 32 or 
			inmem.inmem_bram.ram_s($i) = 64 or 
			inmem.inmem_bram.ram_s($i) = 128 
			"
	}
}


################################################################################
# CHECK FOR CONFLICTS, ENABLE DEAD_END PROP
################################################################################
check_assumptions -show -dead_end
# task -create dead_end -set -source_task iva_debug -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy iva_debug:::noDeadEnd

################################################################################
# Liveness task
################################################################################
# task -create <embedded>_live -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy <embedded>::top.chk_top.ast_pb_start_live <embedded>::top.chk_top.ast_pp_start_live <embedded>::top.chk_top.ast_pb_start_live:precondition1 <embedded>::top.chk_top.ast_pp_start_live:precondition1

# task -create iva_debug_live -set -source_task iva_debug -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy iva_debug::top.chk_top.ast_pb_start_live iva_debug::top.chk_top.ast_pb0_finish_live iva_debug::top.chk_top.ast_pb1_finish_live iva_debug::top.chk_top.ast_pp_start_live iva_debug::top.chk_top.ast_pp_finish_live iva_debug::top.chk_top.ast_pp_finish_live:precondition1 iva_debug::top.chk_top.ast_pb_start_live:precondition1 iva_debug::top.chk_top.ast_pb0_finish_live:precondition1 iva_debug::top.chk_top.ast_pp_start_live:precondition1 iva_debug::top.chk_top.ast_pb1_finish_live:precondition1
################################################################################
# CONVERGENCE, PROOF STRUCTURE cmds
################################################################################

# proof_structure -init CSA_CASE_SPLIT -copy_all -from di_convergence
# proof_structure -create case_split -from DI_PB0_CS_IVA_SBP -condition {chk_top.pb_byte_cnt = x"0"} -op_name OP_B -imp_name {OP0_B0 OP0_B0.completeness_check_0}
#
################################################################################
# HELPER TASK - moved to create_task.tcl - critical
################################################################################
#task -create lv1_help -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
#	<embedded>::top.chk_top.ast_ctrl2_read_help 
#	<embedded>::top.chk_top.ast_ctrl2_read_help:precondition1
#	<embedded>::top.chk_top.ast_idle_pbsr_help 
#	<embedded>::top.chk_top.ast_idle_pbsr_help:precondition1
#	<embedded>::top.chk_top.ast_pbsr_cr_help 
#	<embedded>::top.chk_top.ast_pbsr_cr_help:precondition1
#	<embedded>::top.chk_top.ast_cr_cs_help 
#	<embedded>::top.chk_top.ast_cr_cs_help:precondition1
#	<embedded>::top.chk_top.ast_ctrl2_ex_slave_help 
#	<embedded>::top.chk_top.ast_ctrl2_ex_slave_help:precondition1
#}
################################################################################
## END
################################################################################
# assume -bound 1 -name asm_iva_cont_state_sst {subsys.main_controller.state_reg = 0}
# include create_task.tcl
include ps_lv3_di.tcl

################################################################################
## PROVE
################################################################################
# Inititiate using M engine
#
# prove -task crc_debug -engine_mode {M} -bg
# prove -bg -task {crc_debug}
# prove -bg -task {iva_debug}
# prove -bg -all
# prove -bg -task {<embedded>_live}
# prove -bg -task {iva_debug_live}
################################################################################

################################################################################
## DEEP BUG HUNTING
################################################################################
# prove the existing trace as initial value for another formal proof.

# prove -from iva_debug::top.chk_top.cov_2pb0 -task . -bg
################################################################################


################################################################################
# START COVERAGE ANALYSIS
################################################################################
# check_cov -measure -task {<embedded>} -bg

################################################################################
# FORMAL SAFETY APP COMMANDS
################################################################################
#
# check_fsv -fault -add subsys.parser.axi_read_data_s(4) -type SA1 -silent
# ADD FAULTS
# check_fsv -fault -add outmem.slave_axi_cont_inmem.axi_rdata(4) -type SA1 -silent
# ADD STROBES
# check_fsv -strobe -add outmem.S_AXI_RDATA -functional
# check_fsv -strobe -add subsys.parser.header_reg -functional
# check_fsv -strobe -add subsys.parser.hamming_parity_check_out_s -checker -checker_mode diff
# set_fsv_generate_detectability On; set_fsv_clock_cycle_time 0
# set_fsv_generate_always_propagated On; set_fsv_generate_always_detected On; set_fsv_clock_cycle_time 0
# check_fsv -structural
# check_fsv -generate
# check_fsv -prove

## Use the existing trace as initial value for another formal proof.
#prove -from <embedded>::top.chk_top.cov_no_ecc_uncorr_err -task . -bg
################################################################################
# Formal Profiler
################################################################################
# formal_profiler -property <prop> -viewer
