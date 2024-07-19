
# Create coverage task and add relevant checkers
task -create coverage -set -source_task iva_debug -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy {
	<embedded>::top.chk_top.*coverage*

	<embedded>::top.subsys.intcon.chk_axi_prot_pb0.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_pb1.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_pp.ast_axi*_r_* 
	<embedded>::top.subsys.intcon.chk_axi_prot_pp.ast_axi*_ar_* 
	<embedded>::top.subsys.intcon.chk_axi_prot_ctrl.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_exreg.ast_axi* 
	<embedded>::top.subsys.intcon.chk_axi_prot_reg.ast_axi* 
}
cover -remove *


check_cov -waiver -add -instance chk_top -comment {Checker module}
check_cov -waiver -add -instance subsys.packet_builder0.chk_data_integrity -comment {Added by GUI, apply waiver on instance 'subsys.packet_builder0.chk_data_integrity'}

# check_cov -measure -max_jobs 5 -task {coverage} -bg
# Waive memories
# check_cov -waiver -add -instance inmem -comment {Added by GUI, apply waiver on instance 'inmem'}
# check_cov -waiver -add -instance outmem -comment {Added by GUI, apply waiver on instance 'outmem'}