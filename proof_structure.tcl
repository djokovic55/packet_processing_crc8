
# proof_structure -init CSA_CASE_SPLIT -copy_all -from cont_stopat_debug_01

# loop through operations
#for {set op 0} {$op < 3} {incr op} {
#  # loop through byte count
#	for {set bc 0} {$bc < 16} {incr bc} {
#		proof_structure -create case_split -from CSA_CASE_SPLIT -condition "int(chk_top.pb_data_sel) == $op and int(chk_top.pb_byte_cnt) == $bc" -property {ast_pb0_di_tcl} -op_name CS_OP_B -imp_name "CS_OP${op}_B${bc}"
#	}
#}

