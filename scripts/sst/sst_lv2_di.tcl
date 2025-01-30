
task -create lv2_ctrl2_help -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
	<embedded>::top.chk_top.ast_top_reg_pb0_addr_in
	<embedded>::top.chk_top.ast*lv2_help_high
	<embedded>::top.chk_top.ast*_help_high 
}
cover -remove *
assert -set_helper *_help*
assert -set_helper *_r_*
assert -set_helper *_ar_*
assert -set_helper *_w_*
assert -set_helper *_aw_*
assert -set_helper *lv1_target
assert -mark_proven *_help*
assert -mark_proven *_w_*
assert -mark_proven *_aw_*
assert -mark_proven *_ar_*
assert -mark_proven *_r_*
assert -mark_proven *lv1_target

# prove -property *ast_top_reg_pb0_addr_in -sst 10 -set helper
prove -property *ast_top_reg_pb0_addr_in -with_helpers

#	<embedded>::top.chk_top.ast_ctrl2_read_lv1_target 
#	<embedded>::top.chk_top.ast*_help_high 
#	<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi*ar_stable_araddr* 
#	<embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi*ar_stable_araddr*
#
#<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi*ar_stable_araddr* 
#<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi*aw_stable_awaddr* 
#<embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi*ar_stable_araddr*
#<embedded>::top.subsys.intcon.chk_axi_prot_reg.ast_axi*aw_stable_awaddr* 
