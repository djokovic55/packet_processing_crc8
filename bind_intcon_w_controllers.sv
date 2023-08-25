

////////////////////////////////////////////////////////////////////////////////
// TOP MODULE CHECKERS
////////////////////////////////////////////////////////////////////////////////

bind top checker_top chk_ctrl(
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


bind top checker_top chk_pb1(
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

bind top checker_top chk_pb0(
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

bind top checker_top chk_pp(
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

////////////////////////////////////////////////////////////////////////////////
// MASTER SIDE INTERCONNECT CHECKERS
////////////////////////////////////////////////////////////////////////////////

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

////////////////////////////////////////////////////////////////////////////////
// SLAVE SIDE INTERCONNECT CHECKERS
////////////////////////////////////////////////////////////////////////////////

bind top.intcon checker_axi_slave chk_axi_slave_inmem(
	.clk(clk),
	.reset(reset), 

	////////////////////////////////////////////////////////////////////////////////
	// SLAVES
	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF INMEM MODULE S1
	////////////////////////////////////////////////////////////////////////////////
	.awaddr(m_axi_int_awaddr_inmem),
	.awlen(m_axi_int_awlen_inmem),
	.awsize(m_axi_int_awsize_inmem),
	.awburst(m_axi_int_awburst_inmem),
	.awvalid(m_axi_int_awvalid_inmem),
	.awready(m_axi_int_awready_inmem),

	// WRITE DATA CHANNEL
	.wdata(m_axi_int_wdata_inmem),
	.wstrb(m_axi_int_wstrb_inmem),
	.wlast(m_axi_int_wlast_inmem),
	.wvalid(m_axi_int_wvalid_inmem),
	.wready(m_axi_int_wready_inmem),

	// WRITE RESPONSE CHANNEL
	.bresp(m_axi_int_bresp_inmem),
	.bvalid(m_axi_int_bvalid_inmem),
	.bready(m_axi_int_bready_inmem),

	// READ ADDRESS CHANNEL
	.araddr(m_axi_int_araddr_inmem),
	.arlen(m_axi_int_arlen_inmem),
	.arsize(m_axi_int_arsize_inmem),
	.arburst(m_axi_int_arburst_inmem),
	.arvalid(m_axi_int_arvalid_inmem),
	.arready(m_axi_int_arready_inmem),

	// READ DATA CHANNEL
	.rdata(m_axi_int_rdata_inmem),
	.rresp(m_axi_int_rresp_inmem),
	.rlast(m_axi_int_rlast_inmem),
	.rvalid(m_axi_int_rvalid_inmem),
	.rready(m_axi_int_rready_inmem)
	////////////////////////////////////////////////////////////////////////////////
);

bind top.intcon checker_axi_slave chk_axi_slave_outmem(
	.clk(clk),
	.reset(reset), 

	////////////////////////////////////////////////////////////////////////////////
	// SLAVES
	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF INMEM MODULE S1
	////////////////////////////////////////////////////////////////////////////////
	.awaddr(m_axi_int_awaddr_outmem),
	.awlen(m_axi_int_awlen_outmem),
	.awsize(m_axi_int_awsize_outmem),
	.awburst(m_axi_int_awburst_outmem),
	.awvalid(m_axi_int_awvalid_outmem),
	.awready(m_axi_int_awready_outmem),

	// WRITE DATA CHANNEL
	.wdata(m_axi_int_wdata_outmem),
	.wstrb(m_axi_int_wstrb_outmem),
	.wlast(m_axi_int_wlast_outmem),
	.wvalid(m_axi_int_wvalid_outmem),
	.wready(m_axi_int_wready_outmem),

	// WRITE RESPONSE CHANNEL
	.bresp(m_axi_int_bresp_outmem),
	.bvalid(m_axi_int_bvalid_outmem),
	.bready(m_axi_int_bready_outmem),

	// READ ADDRESS CHANNEL
	.araddr(m_axi_int_araddr_outmem),
	.arlen(m_axi_int_arlen_outmem),
	.arsize(m_axi_int_arsize_outmem),
	.arburst(m_axi_int_arburst_outmem),
	.arvalid(m_axi_int_arvalid_outmem),
	.arready(m_axi_int_arready_outmem),

	// READ DATA CHANNEL
	.rdata(m_axi_int_rdata_outmem),
	.rresp(m_axi_int_rresp_outmem),
	.rlast(m_axi_int_rlast_outmem),
	.rvalid(m_axi_int_rvalid_outmem),
	.rready(m_axi_int_rready_outmem)
	////////////////////////////////////////////////////////////////////////////////
);
////////////////////////////////////////////////////////////////////////////////
// MASTER AXI CHECKER INSIDE MAIN CONTROLLER 
////////////////////////////////////////////////////////////////////////////////
bind top.main_controller.master_axi_cont_ctrl checker_master_axi_cont chk_maxi_cont_ctrl(
	.clk(m_axi_aclk),
	.reset(m_axi_aresetn), 

  .axi_base_address_i(axi_base_address_i),
  .axi_write_address_i(axi_write_address_i),
  .axi_write_init_i(axi_write_init_i),
  .axi_write_data_i(axi_write_data_i),
  .axi_write_vld_i(axi_write_vld_i),
  .axi_write_rdy_o(axi_write_rdy_o),
  .axi_write_done_o(axi_write_done_o),
  .axi_read_address_i(axi_read_address_i),

  .axi_read_init_i(axi_read_init_i),
  .axi_read_data_o(axi_read_data_o),
  .axi_read_vld_o(axi_read_vld_o),
  .axi_read_rdy_i(axi_read_rdy_i),
  .axi_read_last_o(axi_read_last_o),

	.awaddr(m_axi_awaddr),
	.awlen(m_axi_awlen),
	.awsize(m_axi_awsize),
	.awburst(m_axi_awburst),
	.awvalid(m_axi_awvalid),
	.awready(m_axi_awready),

	// WRITE DATA CHANNEL
	.wdata(m_axi_wdata),
	.wstrb(m_axi_wstrb),
	.wlast(m_axi_wlast),
	.wvalid(m_axi_wvalid),
	.wready(m_axi_wready),

	// WRITE RESPONSE CHANNEL
	.bresp(m_axi_bresp),
	.bvalid(m_axi_bvalid),
	.bready(m_axi_bready),

	// READ ADDRESS CHANNEL
	.araddr(m_axi_araddr),
	.arlen(m_axi_arlen),
	.arsize(m_axi_arsize),
	.arburst(m_axi_arburst),
	.arvalid(m_axi_arvalid),
	.arready(m_axi_arready),

	// READ DATA CHANNEL
	.rdata(m_axi_rdata),
	.rresp(m_axi_rresp),
	.rlast(m_axi_rlast),
	.rvalid(m_axi_rvalid),
	.rready(m_axi_rready)
	////////////////////////////////////////////////////////////////////////////////
);

