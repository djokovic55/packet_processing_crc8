################################################################################
# Create case split for di pb0 assertion
################################################################################

# loop through operations
for {set op 0} {$op < 3} {incr op} {
	task -create csa_case_split_op${op} -set -source_task csa_debug -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes 
  # loop through byte count
	for {set bc 0} {$bc < 16} {incr bc} {
		assert -name ast_pb0_di_op${op}_b${bc} "chk_top.pb_data_sel = $op and chk_top.pb_byte_cnt = $bc |-> chk_top.di_err_pb0 = 0"
	}
}
