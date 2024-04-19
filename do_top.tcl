
clear -all
# verif

check_cov -init
set_proof_structure_support_embedded_on_case_split on

# only data integrity checker analysis
# check_cov -init -type {proof bound} -model all -exclude_instance { * } -include_instance {subsys.chk_data_integrity} 
# check_cov -init -type {bound}
analyze -sv09 {checker_top.sv bind_top.sv checker_data_integrity.sv checker_axi.sv checker_fair_int.sv crc_chk_calc.sv checker_di_top.sv}

# src
analyze -vhdl top.vhd top_subsystem.vhd interconnect.vhd arbiter_rr.vhd int_fsm.vhd controller.vhd external_regs.vhd data_memory.vhd master_axi_cont.vhd packet_builder.vhd packet_parser.vhd 
analyze -vhdl regs.vhd slave_axi_cont.vhd 
analyze -vhdl slave_axi_lite_ex_regs_cont.vhd slave_axi_lite_regs_cont.vhd bram.vhd fifo.vhd crc_top.vhd crc8_parallel.vhd hamming_12_8.vhd hamming_check.vhd


# check_fsv -init
elaborate -vhdl -top {top}
clock clk
reset reset


################################################################################
### Apstractions - disable PB1
# stopat subsys.system_regs.pb1_sts_s
# assume -name pb1_always_busy -env {subsys.system_regs.pb1_sts_s = '0'}

################################################################################

### Apstractions - IVAs for Internal Registers 
################################################################################
# PB0 task
################################################################################
# Start register
abstract -init_value subsys.system_regs.pb0_ctrl0_s
# Addr_in register
abstract -init_value subsys.system_regs.pb0_ctrl2_s
assume -bound 1 -env -name asm_iva_pb0_addr_in {subsys.system_regs.pb0_ctrl2_s < x"13"}
assume -bound 1 -env -name asm_iva_top_pb0_addr_in {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl2_s = chk_top.pb_addr_in}

# Config register
abstract -init_value subsys.system_regs.pb0_ctrl3_s
assume -bound 1 -env -name asm_iva_pb0_data_sel {subsys.system_regs.pb0_ctrl3_s(31 downto 28) < x"3" }

assume -bound 1 -env -name asm_iva_top_pb0_byte_cnt {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(3 downto 0) = chk_top.pb_byte_cnt}
assume -bound 1 -env -name asm_iva_top_pb0_pkt_type {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(7 downto 4) = chk_top.pb_pkt_type}
assume -bound 1 -env -name asm_iva_top_pb0_ecc_en {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(8) = chk_top.pb_ecc_en}
assume -bound 1 -env -name asm_iva_top_pb0_crc_en {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(9) = chk_top.pb_crc_en}
assume -bound 1 -env -name asm_iva_top_pb0_ins_ecc_err {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(11 downto 10) = chk_top.pb_ins_ecc_err}
assume -bound 1 -env -name asm_iva_top_pb0_ins_crc_err {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(12) = chk_top.pb_ins_crc_err}
assume -bound 1 -env -name asm_iva_top_pb0_ecc_val {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(16 downto 13) = chk_top.pb_ecc_val}
assume -bound 1 -env -name asm_iva_top_pb0_crc_val {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(24 downto 17) = chk_top.pb_crc_val}
assume -bound 1 -env -name asm_iva_top_pb0_sop_val {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(27 downto 25) = chk_top.pb_sop_val}
assume -bound 1 -env -name asm_iva_top_pb0_data_sel {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl3_s(31 downto 28) = chk_top.pb_data_sel}

# Addr_out register
abstract -init_value subsys.system_regs.pb0_ctrl4_s
assume -bound 1 -env -name asm_iva_pb0_addr_out {subsys.system_regs.pb0_ctrl4_s < x"13"}
assume -bound 1 -env -name asm_iva_top_pb0_addr_out {chk_top.pb0_checker_en |-> subsys.system_regs.pb0_ctrl4_s = chk_top.pb_addr_out}

################################################################################
# PB1 task
################################################################################
# Start register
abstract -init_value subsys.system_regs.pb1_ctrl0_s
# Addr_in register
abstract -init_value subsys.system_regs.pb1_ctrl2_s
assume -bound 1 -env -name asm_iva_pb1_addr_in {subsys.system_regs.pb1_ctrl2_s < x"13"}
assume -bound 1 -env -name asm_iva_top_pb1_addr_in {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl2_s = chk_top.pb_addr_in}

# Config register
abstract -init_value subsys.system_regs.pb1_ctrl3_s
assume -bound 1 -env -name asm_iva_pb1_data_sel {subsys.system_regs.pb1_ctrl3_s(31 downto 28) < x"3" }
assume -bound 1 -env -name asm_iva_top_pb1_byte_cnt {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(3 downto 0) = chk_top.pb_byte_cnt}
assume -bound 1 -env -name asm_iva_top_pb1_pkt_type {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(7 downto 4) = chk_top.pb_pkt_type}
assume -bound 1 -env -name asm_iva_top_pb1_ecc_en {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(8) = chk_top.pb_ecc_en}
assume -bound 1 -env -name asm_iva_top_pb1_crc_en {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(9) = chk_top.pb_crc_en}
assume -bound 1 -env -name asm_iva_top_pb1_ins_ecc_err {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(11 downto 10) = chk_top.pb_ins_ecc_err}
assume -bound 1 -env -name asm_iva_top_pb1_ins_crc_err {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(12) = chk_top.pb_ins_crc_err}
assume -bound 1 -env -name asm_iva_top_pb1_ecc_val {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(16 downto 13) = chk_top.pb_ecc_val}
assume -bound 1 -env -name asm_iva_top_pb1_crc_val {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(24 downto 17) = chk_top.pb_crc_val}
assume -bound 1 -env -name asm_iva_top_pb1_sop_val {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(27 downto 25) = chk_top.pb_sop_val}
assume -bound 1 -env -name asm_iva_top_pb1_data_sel {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl3_s(31 downto 28) = chk_top.pb_data_sel}

# Addr_out register
abstract -init_value subsys.system_regs.pb1_ctrl4_s
assume -bound 1 -env -name asm_iva_pb1_addr_out {subsys.system_regs.pb1_ctrl4_s < x"13"}
assume -bound 1 -env -name asm_iva_top_pb1_addr_out {chk_top.pb1_checker_en |-> subsys.system_regs.pb1_ctrl4_s = chk_top.pb_addr_out}
################################################################################

################################################################################
# PP task
################################################################################
# Start register
abstract -init_value subsys.system_regs.pp_ctrl0_s
# Addr_hdr register
abstract -init_value subsys.system_regs.pp_ctrl2_s
assume -bound 1 -env -name asm_iva_pp_addr_hdr {subsys.system_regs.pp_ctrl2_s < x"13"}
assume -bound 1 -env -name asm_iva_top_pp_addr_hdr {subsys.system_regs.pp_ctrl2_s = chk_top.pp_addr_hdr}

# Ignore ecc errs register
abstract -init_value subsys.system_regs.pp_ctrl3_s
assume -bound 1 -env -name asm_iva_pp_ignore_ecc_err {subsys.system_regs.pp_ctrl3_s = chk_top.pp_ignore_ecc_err}

################################################################################
# INMEM 
################################################################################
abstract -init_value inmem.inmem_bram.ram_s

################################################################################
# TASKs
## Create crc debug task
task -create crc_debug -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy <embedded>::top.chk_top.ast_crc_err <embedded>::top.chk_top.ast_crc_err:precondition1 <embedded>::top.chk_top.ast_crc_no_err <embedded>::top.chk_top.ast_crc_no_err:precondition1 <embedded>::top.chk_top.ast_crc_err_when_ecc_err_exists <embedded>::top.chk_top.ast_crc_err_when_ecc_err_exists:precondition1 <embedded>::top.chk_top.ast_crc_no_err_when_ecc_err_exists <embedded>::top.chk_top.ast_crc_no_err_when_ecc_err_exists:precondition1
################################################################################
## Create iva debug task
task -create iva_debug -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
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
<embedded>::top.chk_top.ast_ecc_corr_err
<embedded>::top.chk_top.ast_ecc_uncorr_err
}
################################################################################
# CHECK FOR CONFLICTS, ENABLE DEAD_END PROP
################################################################################
check_assumptions -show -dead_end
# task -create dead_end -set -source_task iva_debug -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy iva_debug:::noDeadEnd


################################################################################
# CONVERGENCE, PROOF STRUCTURE cmds
################################################################################
task -create di_convergence -set -source_task iva_debug -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy iva_debug::top.chk_top.ast_pb0_di

stopat subsys.parser.*
stopat subsys.packet_builder1.*

stopat subsys.intcon.pp_req
assume -name asm_no_pp_req {subsys.intcon.pp_req = '0'}
stopat subsys.intcon.pb1_req
assume -name asm_no_pb1_req {subsys.intcon.pb1_req = '0'}

assume -name asm_op0_only {chk_top.pb_data_sel = x"0"}
assume -name asm_b0_only {chk_top.pb_byte_cnt = x"0"}

proof_structure -init DI_PB0_CS_IVA_SBP -copy_all -from di_convergence
proof_structure -create case_split -from DI_PB0_CS_IVA_SBP -condition {chk_top.pb_byte_cnt = x"0"} -op_name OP_B -imp_name {OP0_B0 OP0_B0.completeness_check_0}
#
################################################################################
## PROVE
################################################################################
# Inititiate using M engine
#
# prove -task crc_debug -engine_mode {M} -bg
# prove -bg -task {crc_debug}
# prove -bg -task {iva_debug}
# prove -bg -all
################################################################################

################################################################################
## DEEP BUG HUNTING
################################################################################
## prove the existing trace as initial value for another formal proof.
#
# prove -from iva_debug::top.chk_top.cov_2pb0 -task . -bg
################################################################################

### Waive solved unreachable cover points
# check_cov -waiver -add -instance subsys.packet_builder1 -comment {Added by GUI, apply waiver on instance 'subsys.packet_builder1'}
# check_cov -waiver -add -source_file data_memory.vhd -start_line 123 -end_line 360 -comment {Added by GUI, apply waiver on module 'implementation'}
# check_cov -waiver -add -instance inmem -comment {Added by GUI, apply waiver on instance 'inmem'}
# check_cov -waiver -add -instance outmem -comment {Added by GUI, apply waiver on instance 'outmem'}
# check_cov -waiver -add -cover_item_id { 3442 4071 4411 4412 4228 2268 1529 2270 1604 1457 2272 2200 1462 1463 3499 2205 3907 2206 3501 3503 1468 3652 3431 2211 3099 3436 3437} -comment {Added by GUI, apply waiver on ' 3442 4071 4411 4412 4228 2268 1529 2270 1604 1457 2272 2200 1462 1463 3499 2205 3907 2206 3501 3503 1468 3652 3431 2211 3099 3436 3437'}
# check_cov -waiver -add -cover_item_id { 777 925 852 780 929 782 634 783 857 931 784 785 933 861 935 640 828 865 645 869 649 834 910 616 653 840 915 731 657 622 771 846 920 774 628} -comment {Added by GUI, apply waiver on ' 777 925 852 780 929 782 634 783 857 931 784 785 933 861 935 640 828 865 645 869 649 834 910 616 653 840 915 731 657 622 771 846 920 774 628'}
# check_cov -waiver -add -cover_item_id { 1158 1260 1229 1281 1129 1248 1114 1148 1165 1132 1116 1133 1151 1270 1120} -comment {Added by GUI, apply waiver on ' 1158 1260 1229 1281 1129 1248 1114 1148 1165 1132 1116 1133 1151 1270 1120'}
# check_cov -waiver -add -cover_item_id { 1296 1467 1555 1300 1556 1528 1461} -comment {Added by GUI, apply waiver on ' 1296 1467 1555 1300 1556 1528 1461'}
# check_cov -waiver -add -cover_item_id { 1464 1465 1466 1458 1459 1460} -comment {Added by GUI, apply waiver on ' 1464 1465 1466 1458 1459 1460'}
# check_cov -waiver -add -cover_item_id { 1915 1916} -comment {Added by GUI, apply waiver on ' 1915 1916'}
# check_cov -waiver -add -cover_item_id { 1941 1942} -comment {Added by GUI, apply waiver on ' 1941 1942'}
# check_cov -waiver -add -cover_item_id { 1971} -comment {Added by GUI, apply waiver on ' 1971'}
# check_cov -waiver -add -cover_item_id { 2210 2043 2047 2269 2271 2204 2273 2036 2039} -comment {Added by GUI, apply waiver on ' 2210 2043 2047 2269 2271 2204 2273 2036 2039'}
# check_cov -waiver -add -cover_item_id { 2201 2202 2203 2207 2208 2209} -comment {Added by GUI, apply waiver on ' 2201 2202 2203 2207 2208 2209'}
# check_cov -waiver -add -cover_item_id { 1632 1636 1875 1876 1642 1662 1852 1886} -comment {Added by GUI, apply waiver on ' 1632 1636 1875 1876 1642 1662 1852 1886'}
# check_cov -waiver -add -source_file fifo.vhd -start_line 28 -end_line 99 -comment {Added by GUI, apply waiver on module 'rtl'}
# check_cov -waiver -add -cover_item_id { 3536 3570 3537 3571 3572 3522 3573 3574 3524 3575 3508 3576 3509 3550 3653 3552} -comment {Added by GUI, apply waiver on ' 3536 3570 3537 3571 3572 3522 3573 3574 3524 3575 3508 3576 3509 3550 3653 3552'}
# check_cov -waiver -add -cover_item_id { 3767 4024 3771 3924} -comment {Added by GUI, apply waiver on ' 3767 4024 3771 3924'}
# check_cov -waiver -add -cover_item_id { 3015 3067 3035 3022 3024 3143} -comment {Added by GUI, apply waiver on ' 3015 3067 3035 3022 3024 3143'}
# check_cov -waiver -add -cover_item_id { 3502 3435 3504 3267 3270 3441 3274 3278 3500 3262 3263} -comment {Added by GUI, apply waiver on ' 3502 3435 3504 3267 3270 3441 3274 3278 3500 3262 3263'}
# check_cov -waiver -add -cover_item_id { 3434 3438 3439 3440 3432 3433} -comment {Added by GUI, apply waiver on ' 3434 3438 3439 3440 3432 3433'}
# check_cov -waiver -add -cover_item_id { 3204} -comment {Added by GUI, apply waiver on ' 3204'}
# check_cov -waiver -add -cover_item_id { 4124 4345 4245 4128} -comment {Added by GUI, apply waiver on ' 4124 4345 4245 4128'}

################################################################################
# START COVERAGE ANALYSIS
# check_cov -measure -task {<embedded>} -bg

################################################################################
# FORMAL SAFETY APP COMMANDS
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


################################################################################
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
################################################################################
#
