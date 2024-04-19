
set pp_logic_en 1
set pp_req_en 0

set pb1_logic_en 1
set pb1_req_en 0

set ctrl_logic_en 1

set asm_op 1
set op 2 

set asm_bc 1
set bc 15 

set asm_inmem_addr 1
set inmem_addr 0

set asm_outmem_addr 1
set outmem_addr 0

set soft_cs_ast 0

set task_name di_conv_no_mem_op2_b15

task -create $task_name -set -source_task iva_debug -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy iva_debug::top.chk_top.ast_pb0_di

################################################################################
# Abstraction
################################################################################
# Req must be disabled before logic, otherwise false negative occurs
if {$pp_req_en == 0} {
	stopat subsys.intcon.pp_req
	assume -name asm_no_pp_req {subsys.intcon.pp_req = '0'}
	puts "Parser's req disabled."

	if {$pp_logic_en == 0} {
		stopat subsys.parser.*
		puts "Parser's logic removed."
	}
}

if {$pb1_req_en == 0} {
	stopat subsys.intcon.pb1_req
	assume -name asm_no_pb1_req {subsys.intcon.pb1_req = '0'}
	puts "Builder1's req disabled."
	if {$pb1_logic_en == 0} {
		stopat subsys.packet_builder1.*
		puts "Builder1's logic removed."
	}
}

if {$ctrl_logic_en == 0} {
	stopat subsys.main_controller.*
	stopat subsys.intcon.ctrl_req
	assume -name asm_no_ctrl_req {subsys.intcon.ctrl_req = '0'}
	puts "Controller's logic removed."
}
################################################################################
# Configuration
################################################################################

if {$soft_cs_ast == 0} {
	if {$asm_op == 1} {
		assume -name asm_op${op} {chk_top.pb_data_sel = "0010"}
	}

	if {$asm_bc == 1} {
		assume -name asm_b${bc} {chk_top.pb_byte_cnt = "1111"}
	}

	if {$asm_inmem_addr == 1} {
		assume -name asm_inmem${inmem_addr}_val {chk_top.pb_addr_in='0'}
	}

	if {$asm_outmem_addr == 1} {
		assume -name asm_outmem${outmem_addr}_val {chk_top.pb_addr_out='0'}
	}
} else {
	assert -name ast_pb0_di_no_c_op${op}_b${bc}_mem {chk_top.pb_data_sel="0010" and chk_top.pb_byte_cnt="1111" and chk_top.pb_addr_in='0' and chk_top.pb_addr_out='0' |-> chk_top.di_err_pb0='0'}
}


#
