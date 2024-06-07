
task -create lv3_help -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
	<embedded>::top.chk_top.ast_b0_lv3_target

	<embedded>::top.chk_top.ast_top_reg_pb0_addr_in
	<embedded>::top.chk_top.ast_ctrl2_read_lv1_target 
	<embedded>::top.chk_top.ast_ctrl2_read_lv1_target:precondition1

	<embedded>::top.chk_top.ast*reset_help 
	<embedded>::top.chk_top.ast*cfsm_help 
	<embedded>::top.chk_top.ast*base_addr_help 

	<embedded>::top.chk_top.ast*gnt_help 
	<embedded>::top.chk_top.ast*base_addr_reg_help 
	<embedded>::top.chk_top.ast*read_addr_help 

	<embedded>::top.chk_top.ast*axi_help 
	<embedded>::top.chk_top.ast*fifo_help 

	<embedded>::top.chk_top.ast*lv2_help 
	<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi* 
}
cover -remove *
assert -set_helper *_help
assert -set_helper *_r_*
assert -set_helper *_ar_*
assert -set_helper *_w_*
assert -set_helper *_aw_*
assert -set_helper *lv1_target
assert -set_helper *ast_top_reg_pb0_addr_in

assert -mark_proven *_help
assert -mark_proven *_w_*
assert -mark_proven *_aw_*
assert -mark_proven *_ar_*
assert -mark_proven *_r_*
assert -mark_proven *lv1_target
assert -mark_proven *ast_top_reg_pb0_addr_in

prove -property *ast_b0_lv3_target -sst 10 -set helper
#assert -remove *_aw_*
#assert -remove *_w_*
#assert -remove lv1_ctrl2_help::top.chk_top.ast_ctrl2_ex_slave_axi_help

# task -create axi_help -set -source_task lv1_ctrl2_help -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
	#lv1_ctrl2_help::top.chk_top.ast*axi_help 
#}

# task -create lv1_ctrl2_help -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy <embedded>::top.chk_top.ast_ctrl2_read_help

# Target LV2
#	<embedded>::top.chk_top.ast_top_reg_pb0_addr_in 
#	<embedded>::top.chk_top.ast_top_reg_pb0_addr_in:precondition1

# Target LV1
#	<embedded>::top.chk_top.ast_ctrl2_read_help 
#	<embedded>::top.chk_top.ast_ctrl2_read_help:precondition1

# FSM helpers
#	<embedded>::top.chk_top.ast_idle_pbsr_help 
#	<embedded>::top.chk_top.ast_idle_pbsr_help:precondition1
#	<embedded>::top.chk_top.ast_pbsr_cr_help 
#	<embedded>::top.chk_top.ast_pbsr_cr_help:precondition1
#	<embedded>::top.chk_top.ast_cr_cs_help 
#	<embedded>::top.chk_top.ast_cr_cs_help:precondition1

#	<embedded>::top.chk_top.ast*cfsm_help 

# Addr base helpers
#	<embedded>::top.chk_top.ast_idle_base_addr_help 
#	<embedded>::top.chk_top.ast_idle_base_addr_help:precondition1 
#	<embedded>::top.chk_top.ast_pbsr_base_addr_help 
#	<embedded>::top.chk_top.ast_pbsr_base_addr_help:precondition1 
#	<embedded>::top.chk_top.ast_cr_base_addr_help 
#	<embedded>::top.chk_top.ast_cr_base_addr_help:precondition1

#	<embedded>::top.chk_top.ast*base_addr_help 

# AXI helpers

#	<embedded>::top.chk_top.ast*axi_help 
#	<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi* 
#	<embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi* 

