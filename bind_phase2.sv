



bind top checker_top_ex_regs chk_top_ex_regs(
	.clk(clk),
	.reset(reset),

  .ext_pb_ctrl1_conf(ext_pb_ctrl1_con), 
  .ext_pb_ctrl2_conf(ext_pb_ctrl2_con), 
  .ext_pb_ctrl3_conf(ext_pb_ctrl3_con), 
  .ext_pb_ctrl4_conf(ext_pb_ctrl4_con), 

  .ext_pp_ctrl1_conf(ext_pp_ctrl1_con), 
  .ext_pp_ctrl2_conf(ext_pp_ctrl2_con), 
  .ext_pp_ctrl3_conf(ext_pp_ctrl3_con)
)