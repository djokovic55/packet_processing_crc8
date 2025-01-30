
# proof_structure -init CSA_CASE_SPLIT -copy_all -from cont_stopat_debug_01

# loop through operations
#for {set op 0} {$op < 3} {incr op} {
#  # loop through byte count
#	for {set bc 0} {$bc < 16} {incr bc} {
#		proof_structure -create case_split -from CSA_CASE_SPLIT -condition "int(chk_top.pb_data_sel) == $op and int(chk_top.pb_byte_cnt) == $bc" -property {ast_pb0_di_tcl} -op_name CS_OP_B -imp_name "CS_OP${op}_B${bc}"
#	}
#}
#
#
################################################################################
# Create Helper lv5 - Assert correct packet structure in fifo_out PB0
################################################################################

#set str_expr "(id_fifo.fifo_valid\[$i\] && id_fifo.fifo_out\[$i\]\[0\]) |-> (id_fifo.fifo_out\[$i]\[75:68\] == v_top.ID)"
#  assert -helper -name help_check_fifo_tag_data_1_$i $str_expr
proc create_fifo_out_help {} {
	set byte0 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 0 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(0\)\(23 downto 16\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 0\))"
	set byte1 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 1 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(0\)\(31 downto 24\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 1\))"
	set byte2 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 2 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(1\)\(7 downto 0\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 2\))"
	set byte3 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 3 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(1\)\(15 downto 8\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 3\))"

	set byte4 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 4 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(1\)\(23 downto 16\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 4\))"
	set byte5 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 5 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(1\)\(31 downto 24\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 5\))"
	set byte6 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 6 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(2\)\(7 downto 0\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 6\))"
	set byte7 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 7 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(2\)\(15 downto 8\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 7\))"

	set byte8 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 8 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(2\)\(23 downto 16\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 8\))"
	set byte9 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 9 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(2\)\(31 downto 24\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 9\))"
	set byte10 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 10 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(3\)\(7 downto 0\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 10\))"
	set byte11 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 11 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(3\)\(15 downto 8\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 11\))"

	set byte12 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 12 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(3\)\(23 downto 16\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 12\))"
	set byte13 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 13 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(3\)\(31 downto 24\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 13\))"
	set byte14 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 14 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(4\)\(7 downto 0\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 14\))"
	set byte15 "(subsys.packet_builder0.state_reg = OUTMEM_WRITE and chk_top.pb_byte_cnt >= 15 and chk_top.pb0_checker_en) |-> (subsys.packet_builder0.fifo_out.fifo_data_s\(4\)\(15 downto 8\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 15\))"


# for {set pb 0} {$op < 2} {incr pb} { }
	 assert -helper -name ast_pb0_b0_di_fifo_out_help $byte0
	 assert -helper -name ast_pb0_b1_di_fifo_out_help $byte1
	 assert -helper -name ast_pb0_b2_di_fifo_out_help $byte2
	 assert -helper -name ast_pb0_b3_di_fifo_out_help $byte3

	 assert -helper -name ast_pb0_b4_di_fifo_out_help $byte4
	 assert -helper -name ast_pb0_b5_di_fifo_out_help $byte5
	 assert -helper -name ast_pb0_b6_di_fifo_out_help $byte6
	 assert -helper -name ast_pb0_b7_di_fifo_out_help $byte7

	 assert -helper -name ast_pb0_b8_di_fifo_out_help $byte8
	 assert -helper -name ast_pb0_b9_di_fifo_out_help $byte9
	 assert -helper -name ast_pb0_b10_di_fifo_out_help $byte10
	 assert -helper -name ast_pb0_b11_di_fifo_out_help $byte11

	 assert -helper -name ast_pb0_b12_di_fifo_out_help $byte12
	 assert -helper -name ast_pb0_b13_di_fifo_out_help $byte13
	 assert -helper -name ast_pb0_b14_di_fifo_out_help $byte14
	 assert -helper -name ast_pb0_b15_di_fifo_out_help $byte15
}

proc create_outmem_help {} {
	task -create pb0_di_op2_outmem_help -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy <embedded>::top.chk_top.ast_pb0_op2_di

	
	# Only for OP2
	set byte0 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 0 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 2\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 0\))"
	set byte1 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 1 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 3\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 1\))"
	set byte2 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 2 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 4\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 2\))"
	set byte3 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 3 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 5\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 3\))"
	set byte4 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 4 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 6\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 4\))"
	set byte5 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 5 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 7\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 5\))"
	set byte6 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 6 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 8\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 6\))"
	set byte7 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 7 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 9\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 7\))"
	set byte8 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 8 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 10\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 8\))"
	set byte9 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 9 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 11\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 9\))"
	set byte10 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 10 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 12\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 10\))"
	set byte11 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 11 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 13\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 11\))"
	set byte12 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 12 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 14\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 12\))"
	set byte13 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 13 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 15\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 13\))"
	set byte14 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 14 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 16\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 14\))"
	set byte15 "(chk_top.pb_data_sel = 2 and subsys.packet_builder0.irq_O = 1 and chk_top.pb_byte_cnt >= 15 and chk_top.pb0_checker_en) |-> (outmem.inmem_bram.ram_s\(chk_top.pb_addr_out + 17\) = inmem.inmem_bram.ram_s\(chk_top.pb_addr_in + 15\))"

	 assert -helper -name ast_pb0_b0_op2_di_outmem_help $byte0
	 assert -helper -name ast_pb0_b1_op2_di_outmem_help $byte1
	 assert -helper -name ast_pb0_b2_op2_di_outmem_help $byte2
	 assert -helper -name ast_pb0_b3_op2_di_outmem_help $byte3
	 assert -helper -name ast_pb0_b4_op2_di_outmem_help $byte4
	 assert -helper -name ast_pb0_b5_op2_di_outmem_help $byte5
	 assert -helper -name ast_pb0_b6_op2_di_outmem_help $byte6
	 assert -helper -name ast_pb0_b7_op2_di_outmem_help $byte7
	 assert -helper -name ast_pb0_b8_op2_di_outmem_help $byte8
	 assert -helper -name ast_pb0_b9_op2_di_outmem_help $byte9
	 assert -helper -name ast_pb0_b10_op2_di_outmem_help $byte10
	 assert -helper -name ast_pb0_b11_op2_di_outmem_help $byte11
	 assert -helper -name ast_pb0_b12_op2_di_outmem_help $byte12
	 assert -helper -name ast_pb0_b13_op2_di_outmem_help $byte13
	 assert -helper -name ast_pb0_b14_op2_di_outmem_help $byte14
	 assert -helper -name ast_pb0_b15_op2_di_outmem_help $byte15

	check_assumptions -show -dead_end
	# assume -from_assert pb0_di_outmem_help::ast_pb0_b0_di_outmem_help pb0_di_outmem_help::ast_pb0_b1_di_outmem_help pb0_di_outmem_help::ast_pb0_b2_di_outmem_help pb0_di_outmem_help::ast_pb0_b3_di_outmem_help pb0_di_outmem_help::ast_pb0_b4_di_outmem_help pb0_di_outmem_help::ast_pb0_b5_di_outmem_help pb0_di_outmem_help::ast_pb0_b6_di_outmem_help pb0_di_outmem_help::ast_pb0_b7_di_outmem_help pb0_di_outmem_help::ast_pb0_b8_di_outmem_help pb0_di_outmem_help::ast_pb0_b9_di_outmem_help pb0_di_outmem_help::ast_pb0_b10_di_outmem_help pb0_di_outmem_help::ast_pb0_b11_di_outmem_help pb0_di_outmem_help::ast_pb0_b12_di_outmem_help pb0_di_outmem_help::ast_pb0_b13_di_outmem_help pb0_di_outmem_help::ast_pb0_b14_di_outmem_help pb0_di_outmem_help::ast_pb0_b15_di_outmem_help
} 

create_outmem_help
