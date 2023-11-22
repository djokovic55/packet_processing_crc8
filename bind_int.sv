
////////////////////////////////////////////////////////////////////////////////
// BIND Interconnect with master and slave controllers 
////////////////////////////////////////////////////////////////////////////////

bind interconnect master_axi_cont master_ctrl(
	.m_axi_aclk(clk),
	.m_axi_aresetn(reset), 

	.m_axi_awaddr(s_axi_int_awaddr_ctrl),
	.m_axi_awlen(s_axi_int_awlen_ctrl),
	.m_axi_awsize(s_axi_int_awsize_ctrl),
	.m_axi_awburst(s_axi_int_awburst_ctrl),
	.m_axi_awvalid(s_axi_int_awvalid_ctrl),
	.m_axi_awready(s_axi_int_awready_ctrl),

	// WRITE DATA CHANNEL
	.m_axi_wdata(s_axi_int_wdata_ctrl),
	.m_axi_wstrb(s_axi_int_wstrb_ctrl),
	.m_axi_wlast(s_axi_int_wlast_ctrl),
	.m_axi_wvalid(s_axi_int_wvalid_ctrl),
	.m_axi_wready(s_axi_int_wready_ctrl),

	// WRITE RESPONSE CHANNEL
	.m_axi_bresp(s_axi_int_bresp_ctrl),
	.m_axi_bvalid(s_axi_int_bvalid_ctrl),
	.m_axi_bready(s_axi_int_bready_ctrl),

	// READ ADDRESS CHANNEL
	.m_axi_araddr(s_axi_int_araddr_ctrl),
	.m_axi_arlen(s_axi_int_arlen_ctrl),
	.m_axi_arsize(s_axi_int_arsize_ctrl),
	.m_axi_arburst(s_axi_int_arburst_ctrl),
	.m_axi_arvalid(s_axi_int_arvalid_ctrl),
	.m_axi_arready(s_axi_int_arready_ctrl),

	// READ DATA CHANNEL
	.m_axi_rdata(s_axi_int_rdata_ctrl),
	.m_axi_rresp(s_axi_int_rresp_ctrl),
	.m_axi_rlast(s_axi_int_rlast_ctrl),
	.m_axi_rvalid(s_axi_int_rvalid_ctrl),
	.m_axi_rready(s_axi_int_rready_ctrl)
);

bind interconnect master_axi_cont master_pb0(
	.m_axi_aclk(clk),
	.m_axi_aresetn(reset), 

	.m_axi_awaddr(s_axi_int_awaddr_pb0),
	.m_axi_awlen(s_axi_int_awlen_pb0),
	.m_axi_awsize(s_axi_int_awsize_pb0),
	.m_axi_awburst(s_axi_int_awburst_pb0),
	.m_axi_awvalid(s_axi_int_awvalid_pb0),
	.m_axi_awready(s_axi_int_awready_pb0),

	// WRITE DATA CHANNEL
	.m_axi_wdata(s_axi_int_wdata_pb0),
	.m_axi_wstrb(s_axi_int_wstrb_pb0),
	.m_axi_wlast(s_axi_int_wlast_pb0),
	.m_axi_wvalid(s_axi_int_wvalid_pb0),
	.m_axi_wready(s_axi_int_wready_pb0),

	// WRITE RESPONSE CHANNEL
	.m_axi_bresp(s_axi_int_bresp_pb0),
	.m_axi_bvalid(s_axi_int_bvalid_pb0),
	.m_axi_bready(s_axi_int_bready_pb0),

	// READ ADDRESS CHANNEL
	.m_axi_araddr(s_axi_int_araddr_pb0),
	.m_axi_arlen(s_axi_int_arlen_pb0),
	.m_axi_arsize(s_axi_int_arsize_pb0),
	.m_axi_arburst(s_axi_int_arburst_pb0),
	.m_axi_arvalid(s_axi_int_arvalid_pb0),
	.m_axi_arready(s_axi_int_arready_pb0),

	// READ DATA CHANNEL
	.m_axi_rdata(s_axi_int_rdata_pb0),
	.m_axi_rresp(s_axi_int_rresp_pb0),
	.m_axi_rlast(s_axi_int_rlast_pb0),
	.m_axi_rvalid(s_axi_int_rvalid_pb0),
	.m_axi_rready(s_axi_int_rready_pb0)
);

bind interconnect master_axi_cont master_pb1(
	.m_axi_aclk(clk),
	.m_axi_aresetn(reset), 

	.m_axi_awaddr(s_axi_int_awaddr_pb1),
	.m_axi_awlen(s_axi_int_awlen_pb1),
	.m_axi_awsize(s_axi_int_awsize_pb1),
	.m_axi_awburst(s_axi_int_awburst_pb1),
	.m_axi_awvalid(s_axi_int_awvalid_pb1),
	.m_axi_awready(s_axi_int_awready_pb1),

	// WRITE DATA CHANNEL
	.m_axi_wdata(s_axi_int_wdata_pb1),
	.m_axi_wstrb(s_axi_int_wstrb_pb1),
	.m_axi_wlast(s_axi_int_wlast_pb1),
	.m_axi_wvalid(s_axi_int_wvalid_pb1),
	.m_axi_wready(s_axi_int_wready_pb1),

	// WRITE RESPONSE CHANNEL
	.m_axi_bresp(s_axi_int_bresp_pb1),
	.m_axi_bvalid(s_axi_int_bvalid_pb1),
	.m_axi_bready(s_axi_int_bready_pb1),

	// READ ADDRESS CHANNEL
	.m_axi_araddr(s_axi_int_araddr_pb1),
	.m_axi_arlen(s_axi_int_arlen_pb1),
	.m_axi_arsize(s_axi_int_arsize_pb1),
	.m_axi_arburst(s_axi_int_arburst_pb1),
	.m_axi_arvalid(s_axi_int_arvalid_pb1),
	.m_axi_arready(s_axi_int_arready_pb1),

	// READ DATA CHANNEL
	.m_axi_rdata(s_axi_int_rdata_pb1),
	.m_axi_rresp(s_axi_int_rresp_pb1),
	.m_axi_rlast(s_axi_int_rlast_pb1),
	.m_axi_rvalid(s_axi_int_rvalid_pb1),
	.m_axi_rready(s_axi_int_rready_pb1)
);

bind interconnect master_axi_cont master_pp(
	.m_axi_aclk(clk),
	.m_axi_aresetn(reset), 

	.m_axi_awaddr(s_axi_int_awaddr_pp),
	.m_axi_awlen(s_axi_int_awlen_pp),
	.m_axi_awsize(s_axi_int_awsize_pp),
	.m_axi_awburst(s_axi_int_awburst_pp),
	.m_axi_awvalid(s_axi_int_awvalid_pp),
	.m_axi_awready(s_axi_int_awready_pp),

	// WRITE DATA CHANNEL
	.m_axi_wdata(s_axi_int_wdata_pp),
	.m_axi_wstrb(s_axi_int_wstrb_pp),
	.m_axi_wlast(s_axi_int_wlast_pp),
	.m_axi_wvalid(s_axi_int_wvalid_pp),
	.m_axi_wready(s_axi_int_wready_pp),

	// WRITE RESPONSE CHANNEL
	.m_axi_bresp(s_axi_int_bresp_pp),
	.m_axi_bvalid(s_axi_int_bvalid_pp),
	.m_axi_bready(s_axi_int_bready_pp),

	// READ ADDRESS CHANNEL
	.m_axi_araddr(s_axi_int_araddr_pp),
	.m_axi_arlen(s_axi_int_arlen_pp),
	.m_axi_arsize(s_axi_int_arsize_pp),
	.m_axi_arburst(s_axi_int_arburst_pp),
	.m_axi_arvalid(s_axi_int_arvalid_pp),
	.m_axi_arready(s_axi_int_arready_pp),

	// READ DATA CHANNEL
	.m_axi_rdata(s_axi_int_rdata_pp),
	.m_axi_rresp(s_axi_int_rresp_ctrl),
	.m_axi_rlast(s_axi_int_rlast_pp),
	.m_axi_rvalid(s_axi_int_rvalid_pp),
	.m_axi_rready(s_axi_int_rready_pp)
);
////////////////////////////////////////////////////////////////////////////////
// BIND master axi controllers with master checker
////////////////////////////////////////////////////////////////////////////////

bind master_axi_cont checker_master chk_master(
  .clk(m_axi_aclk),
  .reset(m_axi_aresetn),

  .axi_base_address_i(axi_base_address_i),
  .axi_write_address_i(axi_write_address_i),
  .axi_write_init_i(axi_write_init_i),
  .axi_write_data_i(axi_write_data_i),
  .axi_write_vld_i(axi_write_vld_i),
  .axi_write_rdy_o(axi_write_rdy_o),
  .axi_write_done_o(axi_write_done_o),

  .axi_read_init_i(axi_read_init_i),
  .axi_read_address_i(axi_read_addr),
  .axi_read_data_o(axi_read_data_o),
  .axi_read_vld_o(axi_read_vld_o),
  .axi_read_rdy_i(axi_read_rdy_i),
  .axi_read_last_o(axi_read_last_o)
);

////////////////////////////////////////////////////////////////////////////////
// BIND round robin arbiter with fairness checker
////////////////////////////////////////////////////////////////////////////////

bind arbiter_rr checker_fair_int chk_fairness(
	.clk(clk),
	.reset(resetn),

	.req(req),
	.gnt(gnt)
);
////////////////////////////////////////////////////////////////////////////////
// BIND axi controllers with axi protocol checker
////////////////////////////////////////////////////////////////////////////////

bind master_axi_cont checker_axi chk_axi_prot(
	.clk(m_axi_aclk),
	.reset(m_axi_aresetn), 

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

bind slave_axi_cont checker_axi chk_axi_prot(
	.clk(s_axi_aclk),
	.reset(s_axi_aresetn), 

	.awaddr(s_axi_awaddr),
	.awlen(s_axi_awlen),
	.awsize(s_axi_awsize),
	.awburst(s_axi_awburst),
	.awvalid(s_axi_awvalid),
	.awready(s_axi_awready),

	// WRITE DATA CHANNEL
	.wdata(s_axi_wdata),
	.wstrb(s_axi_wstrb),
	.wlast(s_axi_wlast),
	.wvalid(s_axi_wvalid),
	.wready(s_axi_wready),

	// WRITE RESPONSE CHANNEL
	.bresp(s_axi_bresp),
	.bvalid(s_axi_bvalid),
	.bready(s_axi_bready),

	// READ ADDRESS CHANNEL
	.araddr(s_axi_araddr),
	.arlen(s_axi_arlen),
	.arsize(s_axi_arsize),
	.arburst(s_axi_arburst),
	.arvalid(s_axi_arvalid),
	.arready(s_axi_arready),

	// READ DATA CHANNEL
	.rdata(s_axi_rdata),
	.rresp(s_axi_rresp),
	.rlast(s_axi_rlast),
	.rvalid(s_axi_rvalid),
	.rready(s_axi_rready)
	////////////////////////////////////////////////////////////////////////////////
);
