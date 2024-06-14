proof_structure -init PB0_DI -from lv5_help -copy_all 

set lv1_helpers "
								top.chk_top.ast*reset_help 
								top.chk_top.ast*cfsm_help 
								top.chk_top.ast*base_addr_help 
								top.chk_top.ast*gnt_help 
								top.chk_top.ast*base_addr_reg_help 
								top.chk_top.ast*read_addr_help 
								top.chk_top.ast*axi_help 
								top.chk_top.ast*fifo_help 
								top.subsys.intcon.chk_axi_prot_ctrl.ast_axi* 
								top.subsys.intcon.chk_axi_prot_exreg.ast_axi* 
								"

proof_structure -create assume_guarantee \
								-from PB0_DI \
								-op_name LV1 \
								-imp_name {LV1.G LV1.A} \
								-property [list ${lv1_helpers} top.chk_top.ast_ctrl2_read_lv1_target]


