proc run_sst_pb0_proc {} {
	task -create lv5_help -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
		<embedded>::top.chk_top.ast_pb0_di*
		<embedded>::top.chk_top.ast*lv5_help_high*
		<embedded>::top.chk_top.ast*lv4_help_high*
		<embedded>::top.chk_top.ast*lv2_help_high*
		<embedded>::*ast_axi* 
	}

	cover -remove *
	assert -set_helper *help_high*
	assert -set_helper *ast_axi*
	assert -mark_proven *help_high*
	assert -mark_proven *ast_axi*

	# Generate SST CEX for target property
	prove -property *ast_pb0_di* -sst 10 -set helper 
	# Prove target property with helpers
	prove -property *ast_pb0_di* -with_helpers 

	# Prove new helpers candidates
	task -create lv5_G -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {<embedded>::top.chk_top.*lv5*new*}
	prove -bg -task {lv5_G}
}