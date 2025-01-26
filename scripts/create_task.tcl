
task -create lv1_ctrl2_help -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
	<embedded>::top.chk_top.ast_ctrl2_read_lv1_target 

	<embedded>::top.chk_top.ast*_help_high 
	<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi*ar_stable_araddr* 
	<embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi*ar_stable_araddr*
}
cover -remove *
assert -set_helper *_help*
assert -set_helper *_r_*
assert -set_helper *_ar_*
assert -set_helper *_w_*
assert -set_helper *_aw_*
assert -mark_proven *_help*
assert -mark_proven *_w_*
assert -mark_proven *_aw_*
assert -mark_proven *_ar_*
assert -mark_proven *_r_*

# prove -property *target -sst 8 -set helper
prove -property *target -with_helpers

