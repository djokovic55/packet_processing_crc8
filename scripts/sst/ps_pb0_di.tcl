proc run_proof_structure_proc {} {
	task -create PS_SETUP -set -source_task <embedded> -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy_assert -set 

	# Root node
	proof_structure -init ROOT -from PS_SETUP -copy_all

	# In proof structure feature all helpers should be used in top guarantee node 
	# From there some of them will become targets or remain helpers on sublevels

	# Top node
	set main_target "{*ast_pb0_di*}"
	set main_helpers "{*lv5_help_high*} {*lv4_help_high*} {*lv2_help_high*} {*ast_axi*}"
	proof_structure -create assume_guarantee \
					-from ROOT \
					-op_name MAIN \
					-imp_name {MAIN.G MAIN.A} \
					-property [list ${main_helpers} $main_target]

	prove -bg -task {MAIN.A}
}
