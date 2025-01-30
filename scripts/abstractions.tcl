
################################################################################
# Apstraction - IVAs for Internal Registers 
################################################################################
# Copy main embedded task and apply IVA on registers
proc registers_iva_abs_proc {} {
	## Create iva registers_iva task
	# task -create registers_iva -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy * 
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
# Apstraction - REMOVE CONTROLLER LOGIC, Stopats for Internal Registers 
# It is important to have the same configuration on top and in registers 
# in order to have coherent data in both checker and rtl
################################################################################
proc blackbox_controller_abs_proc {} {

	## Create separate task where controller logic is removed
	# task -create controller_blackbox -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy_assert -set 

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


################################################################################
# Assume inital values for memory locations
################################################################################
proc inmem_iva_abs_proc {} {
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
# Apstraction - PB1 always busy
################################################################################
proc disable_pb1_abs_proc {} {
	stopat subsys.system_regs.pb1_sts_s
	assume -name pb1_always_busy {subsys.system_regs.pb1_sts_s = '0'}
}