
task -create lv5_help -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
	<embedded>::top.chk_top.ast_pb0_di
	<embedded>::top.chk_top.*pb0*_lv4_new_target*
	<embedded>::top.chk_top.ast_lv3_target
	<embedded>::top.chk_top.ast*_help_high*

	<embedded>::top.subsys.intcon.chk_axi_prot_pb0.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_reg.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_inmem.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_outmem.ast_axi* 
}
cover -remove *
assert -set_helper *_help_high*
assert -set_helper *prot*ast_axi*
assert -set_helper *lv1_target
assert -set_helper *ast_top_reg_pb0_addr_in
assert -set_helper *ast_lv3_target
assert -set_helper *pb0*_lv4_new_target*

assert -mark_proven *_help_high*
assert -mark_proven *prot*ast_axi*
assert -mark_proven *lv1_target
assert -mark_proven *ast_top_reg_pb0_addr_in
assert -mark_proven *ast_lv3_target
assert -mark_proven *pb0*_lv4_new_target*

# Generate SST trace

# prove -property *ast_packet_integrity -sst 10 -set helper
prove -property *ast_pb0_di -sst 10 -set helper
# Prove target property with helpers
# prove -property *ast_pb0_di -with_helpers

# Check new helpers
task -create lv5_G -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {<embedded>::top.chk_top.*lv5*new*}
prove -bg -task {lv5_G}
# task -create lv4_new_target -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {<embedded>::top.chk_top.*_lv4_new_target* <embedded>::top.subsys.chk_data_integrity.ast_packet_integrity}