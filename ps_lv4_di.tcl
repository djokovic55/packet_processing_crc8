
# task -create lv4_G -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
# 	<embedded>::top.chk_top.ast_hs_when_pkt_arrives_lv4_help_high_new
# 	<embedded>::top.chk_top.ast_hs_when_pkt_arrives_lv4_help_high_new:precondition1 
# 	<embedded>::top.chk_top.ast_wpulse_when_pkt_arrives_lv4_help_high_new 
# 	<embedded>::top.chk_top.ast_wpulse_when_pkt_arrives_lv4_help_high_new:precondition1
# }


	# <embedded>::top.subsys.chk_data_integrity.ast_packet_integrity
task -create lv4_help -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
	<embedded>::top.chk_top.*pb0*_lv4_new_target*
	<embedded>::top.chk_top.ast_lv3_target
	<embedded>::top.chk_top.ast*_help_high*

	<embedded>::top.subsys.intcon.chk_axi_prot_pb0.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi* 
}
cover -remove *
# Remove all axi properties except stable araddr and address handshake
# assert -remove *_aw_*
# assert -remove *_w_*
# assert -remove *_b_*
# assert -remove *_r_*
# assert -remove *_arlen*
# assert -remove *_arsize*
# assert -remove *_arburst*
# assert -remove *_rlast*

assert -set_helper *_help_high*
assert -set_helper *prot*ast_axi*
assert -set_helper *lv1_target
assert -set_helper *ast_top_reg_pb0_addr_in
assert -set_helper *ast_lv3_target

assert -mark_proven *_help_high*
assert -mark_proven *prot*ast_axi*
assert -mark_proven *lv1_target
assert -mark_proven *ast_top_reg_pb0_addr_in
assert -mark_proven *ast_lv3_target


# Generate SST trace

# prove -property *ast_packet_integrity -sst 10 -set helper
prove -property *pb0*_lv4_new_target* -sst 10 -set helper
# Prove target property with helpers
# prove -property *pb0*_lv4_new_target* -with_helpers

# Check new helpers
task -create lv4_G -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {<embedded>::top.chk_top.ast*_help_high_new*}
prove -bg -task {lv4_G}
# task -create lv4_new_target -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {<embedded>::top.chk_top.*_lv4_new_target* <embedded>::top.subsys.chk_data_integrity.ast_packet_integrity}