

bind top checker_master_axi_cont chk_cont_ctrl(
  .clk(clk),
  .reset(reset),

  .axi_base_address_i(axi_base_address_i_ctrl),
  .axi_write_address_i(axi_write_address_i_ctrl),
  .axi_write_init_i(axi_write_init_i_ctrl),
  .axi_write_data_i(axi_write_data_i_ctrl),
  .axi_write_vld_i(axi_write_vld_i_ctrl),
  .axi_write_rdy_o(axi_write_rdy_o_ctrl),
  .axi_write_done_o(axi_write_done_o_ctrl),
  .axi_read_address_i(axi_read_address_i_ctrl),

  .axi_read_init_i(axi_read_init_i_ctrl),
  .axi_read_data_o(axi_read_data_o_ctrl),
  .axi_read_vld_o(axi_read_vld_o_ctrl),
  .axi_read_rdy_i(axi_read_rdy_i_ctrl),
  .axi_read_last_o(axi_read_last_o_ctrl)
);


bind top checker_master_axi_cont chk_cont_pb1(
  .clk(clk),
  .reset(reset),

  .axi_base_address_i(axi_base_address_i_pb1),
  .axi_write_address_i(axi_write_address_i_pb1),
  .axi_write_init_i(axi_write_init_i_pb1),
  .axi_write_data_i(axi_write_data_i_pb1),
  .axi_write_vld_i(axi_write_vld_i_pb1),
  .axi_write_rdy_o(axi_write_rdy_o_pb1),
  .axi_write_done_o(axi_write_done_o_pb1),
  .axi_read_address_i(axi_read_address_i_pb1),

  .axi_read_init_i(axi_read_init_i_pb1),
  .axi_read_data_o(axi_read_data_o_pb1),
  .axi_read_vld_o(axi_read_vld_o_pb1),
  .axi_read_rdy_i(axi_read_rdy_i_pb1),
  .axi_read_last_o(axi_read_last_o_pb1)
);

bind top checker_master_axi_cont chk_cont_pb0(
  .clk(clk),
  .reset(reset),

  .axi_base_address_i(axi_base_address_i_pb0),
  .axi_write_address_i(axi_write_address_i_pb0),
  .axi_write_init_i(axi_write_init_i_pb0),
  .axi_write_data_i(axi_write_data_i_pb0),
  .axi_write_vld_i(axi_write_vld_i_pb0),
  .axi_write_rdy_o(axi_write_rdy_o_pb0),
  .axi_write_done_o(axi_write_done_o_pb0),
  .axi_read_address_i(axi_read_address_i_pb0),

  .axi_read_init_i(axi_read_init_i_pb0),
  .axi_read_data_o(axi_read_data_o_pb0),
  .axi_read_vld_o(axi_read_vld_o_pb0),
  .axi_read_rdy_i(axi_read_rdy_i_pb0),
  .axi_read_last_o(axi_read_last_o_pb0)
);

bind top checker_master_axi_cont chk_cont_pp(
  .clk(clk),
  .reset(reset),

  .axi_base_address_i(axi_base_address_i_pp),
  .axi_write_address_i(axi_write_address_i_pp),
  .axi_write_init_i(axi_write_init_i_pp),
  .axi_write_data_i(axi_write_data_i_pp),
  .axi_write_vld_i(axi_write_vld_i_pp),
  .axi_write_rdy_o(axi_write_rdy_o_pp),
  .axi_write_done_o(axi_write_done_o_pp),
  .axi_read_address_i(axi_read_address_i_pp),

  .axi_read_init_i(axi_read_init_i_pp),
  .axi_read_data_o(axi_read_data_o_pp),
  .axi_read_vld_o(axi_read_vld_o_pp),
  .axi_read_rdy_i(axi_read_rdy_i_pp),
  .axi_read_last_o(axi_read_last_o_pp)
);


bind top.intcon checker_axi chk_axi_ctrl(
	.clk(clk),
	.reset(reset), 

	////////////////////////////////////////////////////////////////////////////////
	// MASTERS
	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF CONTROLLER MODULE M1
	////////////////////////////////////////////////////////////////////////////////
	.awaddr(s_axi_int_awaddr_ctrl),
	.awlen(s_axi_int_awlen_ctrl),
	.awsize(s_axi_int_awsize_ctrl),
	.awburst(s_axi_int_awburst_ctrl),
	.awvalid(s_axi_int_awvalid_ctrl),
	.awready(s_axi_int_awready_ctrl),

	// WRITE DATA CHANNEL
	.wdata(s_axi_int_wdata_ctrl),
	.wstrb(s_axi_int_wstrb_ctrl),
	.wlast(s_axi_int_wlast_ctrl),
	.wvalid(s_axi_int_wvalid_ctrl),
	.wready(s_axi_int_wready_ctrl),

	// WRITE RESPONSE CHANNEL
	.bresp(s_axi_int_bresp_ctrl),
	.bvalid(s_axi_int_bvalid_ctrl),
	.bready(s_axi_int_bready_ctrl),

	// READ ADDRESS CHANNEL
	.araddr(s_axi_int_araddr_ctrl),
	.arlen(s_axi_int_arlen_ctrl),
	.arsize(s_axi_int_arsize_ctrl),
	.arburst(s_axi_int_arburst_ctrl),
	.arvalid(s_axi_int_arvalid_ctrl),
	.arready(s_axi_int_arready_ctrl),

	// READ DATA CHANNEL
	.rdata(s_axi_int_rdata_ctrl),
	.rresp(s_axi_int_rresp_ctrl),
	.rlast(s_axi_int_rlast_ctrl),
	.rvalid(s_axi_int_rvalid_ctrl),
	.rready(s_axi_int_rready_ctrl)
	////////////////////////////////////////////////////////////////////////////////
);

bind top.intcon checker_axi chk_axi_pb0(
	.clk(clk),
	.reset(reset), 

	////////////////////////////////////////////////////////////////////////////////
	// MASTERS
	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF PB0 MODULE M2
	////////////////////////////////////////////////////////////////////////////////
	.awaddr(s_axi_int_awaddr_pb0),
	.awlen(s_axi_int_awlen_pb0),
	.awsize(s_axi_int_awsize_pb0),
	.awburst(s_axi_int_awburst_pb0),
	.awvalid(s_axi_int_awvalid_pb0),
	.awready(s_axi_int_awready_pb0),

	// WRITE DATA CHANNEL
	.wdata(s_axi_int_wdata_pb0),
	.wstrb(s_axi_int_wstrb_pb0),
	.wlast(s_axi_int_wlast_pb0),
	.wvalid(s_axi_int_wvalid_pb0),
	.wready(s_axi_int_wready_pb0),

	// WRITE RESPONSE CHANNEL
	.bresp(s_axi_int_bresp_pb0),
	.bvalid(s_axi_int_bvalid_pb0),
	.bready(s_axi_int_bready_pb0),

	// READ ADDRESS CHANNEL
	.araddr(s_axi_int_araddr_pb0),
	.arlen(s_axi_int_arlen_pb0),
	.arsize(s_axi_int_arsize_pb0),
	.arburst(s_axi_int_arburst_pb0),
	.arvalid(s_axi_int_arvalid_pb0),
	.arready(s_axi_int_arready_pb0),

	// READ DATA CHANNEL
	.rdata(s_axi_int_rdata_pb0),
	.rresp(s_axi_int_rresp_pb0),
	.rlast(s_axi_int_rlast_pb0),
	.rvalid(s_axi_int_rvalid_pb0),
	.rready(s_axi_int_rready_pb0)
	////////////////////////////////////////////////////////////////////////////////
);


bind top.intcon checker_axi chk_axi_pb1(
	.clk(clk),
	.reset(reset), 

	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF PB1 MODULE M3
	////////////////////////////////////////////////////////////////////////////////
	.awaddr(s_axi_int_awaddr_pb1),
	.awlen(s_axi_int_awlen_pb1),
	.awsize(s_axi_int_awsize_pb1),
	.awburst(s_axi_int_awburst_pb1),
	.awvalid(s_axi_int_awvalid_pb1),
	.awready(s_axi_int_awready_pb1),

	// WRITE DATA CHANNEL
	.wdata(s_axi_int_wdata_pb1),
	.wstrb(s_axi_int_wstrb_pb1),
	.wlast(s_axi_int_wlast_pb1),
	.wvalid(s_axi_int_wvalid_pb1),
	.wready(s_axi_int_wready_pb1),

	// WRITE RESPONSE CHANNEL
	.bresp(s_axi_int_bresp_pb1),
	.bvalid(s_axi_int_bvalid_pb1),
	.bready(s_axi_int_bready_pb1),

	// READ ADDRESS CHANNEL
	.araddr(s_axi_int_araddr_pb1),
	.arlen(s_axi_int_arlen_pb1),
	.arsize(s_axi_int_arsize_pb1),
	.arburst(s_axi_int_arburst_pb1),
	.arvalid(s_axi_int_arvalid_pb1),
	.arready(s_axi_int_arready_pb1),

	// READ DATA CHANNEL
	.rdata(s_axi_int_rdata_pb1),
	.rresp(s_axi_int_rresp_pb1),
	.rlast(s_axi_int_rlast_pb1),
	.rvalid(s_axi_int_rvalid_pb1),
	.rready(s_axi_int_rready_pb1)
	////////////////////////////////////////////////////////////////////////////////
);

bind top.intcon checker_axi chk_axi_pp(
	.clk(clk),
	.reset(reset), 

	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF PP MODULE M4
	////////////////////////////////////////////////////////////////////////////////
	.awaddr(s_axi_int_awaddr_pp),
	.awlen(s_axi_int_awlen_pp),
	.awsize(s_axi_int_awsize_pp),
	.awburst(s_axi_int_awburst_pp),
	.awvalid(s_axi_int_awvalid_pp),
	.awready(s_axi_int_awready_pp),

	// WRITE DATA CHANNEL
	.wdata(s_axi_int_wdata_pp),
	.wstrb(s_axi_int_wstrb_pp),
	.wlast(s_axi_int_wlast_pp),
	.wvalid(s_axi_int_wvalid_pp),
	.wready(s_axi_int_wready_pp),

	// WRITE RESPONSE CHANNEL
	.bresp(s_axi_int_bresp_pp),
	.bvalid(s_axi_int_bvalid_pp),
	.bready(s_axi_int_bready_pp),

	// READ ADDRESS CHANNEL
	.araddr(s_axi_int_araddr_pp),
	.arlen(s_axi_int_arlen_pp),
	.arsize(s_axi_int_arsize_pp),
	.arburst(s_axi_int_arburst_pp),
	.arvalid(s_axi_int_arvalid_pp),
	.arready(s_axi_int_arready_pp),

	// READ DATA CHANNEL
	.rdata(s_axi_int_rdata_pp),
	.rresp(s_axi_int_rresp_pp),
	.rlast(s_axi_int_rlast_pp),
	.rvalid(s_axi_int_rvalid_pp),
	.rready(s_axi_int_rready_pp)
	////////////////////////////////////////////////////////////////////////////////
);

