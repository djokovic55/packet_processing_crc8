
task -create lv3_help -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
	<embedded>::top.chk_top.ast_lv3_target
	<embedded>::top.chk_top.ast*help_lv3_new*

	<embedded>::top.chk_top.ast*help_lv3*
	<embedded>::top.chk_top.ast_top_reg_pb0_addr_in
	<embedded>::top.chk_top.ast*lv2_help_high
	<embedded>::top.chk_top.ast*_help_high 
	<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_reg.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_inmem.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_pb0.ast_axi* 
}
cover -remove *
assert -set_helper *_help*
assert -set_helper *prot*ast_axi*
assert -set_helper *lv1_target
assert -set_helper *ast_top_reg_pb0_addr_in

assert -mark_proven *_help*
assert -mark_proven *prot*ast_axi*
assert -mark_proven *lv1_target
assert -mark_proven *ast_top_reg_pb0_addr_in

prove -property *ast_lv3_target -sst 10 -set helper
# prove -property *ast_lv3_target -with_helpers

#assert -remove *_aw_*
#assert -remove *_w_*
#assert -remove lv1_ctrl2_help::top.chk_top.ast_ctrl2_ex_slave_axi_help
#
#	<embedded>::top.chk_top.ast_top_reg_pb0_addr_in
#	<embedded>::top.chk_top.ast_ctrl2_read_lv1_target 
#	<embedded>::top.chk_top.ast_ctrl2_read_lv1_target:precondition1

#	<embedded>::top.chk_top.ast*reset_help 
#	<embedded>::top.chk_top.ast*cfsm_help 
#	<embedded>::top.chk_top.ast*base_addr_help 

#	<embedded>::top.chk_top.ast*gnt_help 
#	<embedded>::top.chk_top.ast*base_addr_reg_help 
#	<embedded>::top.chk_top.ast*read_addr_help 

#	<embedded>::top.chk_top.ast*axi_help 
#	<embedded>::top.chk_top.ast*fifo_help 

#	<embedded>::top.chk_top.ast*lv2_help 
#	<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi* 
#	<embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi* 
