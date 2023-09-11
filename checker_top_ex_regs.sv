
checker  checker_top_ex_regs(
	clk	,
	reset	,

  ext_pb_ctrl1_conf, 
  ext_pb_ctrl2_conf, 
  ext_pb_ctrl3_conf, 
  ext_pb_ctrl4_conf, 

  ext_pp_ctrl1_conf, 
  ext_pp_ctrl2_conf, 
  ext_pp_ctrl3_conf

);

	default 
	clocking @(posedge clk);
	endclocking

	default disable iff reset;

endchecker