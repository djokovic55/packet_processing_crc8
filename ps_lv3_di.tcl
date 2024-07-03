
task -create lv3_help -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
	<embedded>::top.chk_top.ast_lv3_new_target
	<embedded>::top.chk_top.ast*_lv3_help_high*

	<embedded>::top.chk_top.ast*lv2_help_high
	<embedded>::top.subsys.intcon.chk_axi_prot_pb0.ast_axi* 

}
# Remove low impact properties
cover -remove *
assert -remove *_aw_*
assert -remove *_w_*
assert -remove *_b_*
assert -remove *_r_*
assert -remove *_arlen*
assert -remove *_arsize*
assert -remove *_arburst*
assert -remove *_rlast*

# Set all remaining assertions as proved helpers
assert -set_helper *_help_high*
assert -set_helper *prot*ast_axi*
assert -set_helper *lv1_target
assert -set_helper *ast_top_reg_pb0_addr_in

assert -mark_proven *_help_high*
assert -mark_proven *prot*ast_axi*
assert -mark_proven *lv1_target
assert -mark_proven *ast_top_reg_pb0_addr_in

# Generate SST trace
# prove -property *ast_lv3_target -sst 10 -set helper
prove -property *ast_lv3_new_target -sst 10 -set helper
# Prove target property with helpers
prove -property *ast_lv3_new_target -with_helpers

	# <embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi* 
	# <embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi* 
	# <embedded>::top.subsys.intcon.chk_axi_prot_reg.ast_axi* 
	# <embedded>::top.subsys.intcon.chk_axi_prot_inmem.ast_axi* 

	# <embedded>::top.chk_top.ast*help_lv3*
	# <embedded>::top.chk_top.ast*_help_high 
	# <embedded>::top.chk_top.ast_top_reg_pb0_addr_in