
////////////////////////////////////////////////////////////////////////////////
// BIND Interconnect with master controllers 
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
	.m_axi_rresp(s_axi_int_rresp_pp),
	.m_axi_rlast(s_axi_int_rlast_pp),
	.m_axi_rvalid(s_axi_int_rvalid_pp),
	.m_axi_rready(s_axi_int_rready_pp)
);

////////////////////////////////////////////////////////////////////////////////
// BIND Interconnect with master controllers 
////////////////////////////////////////////////////////////////////////////////

bind interconnect slave_axi_cont slave_inmem(
	.s_axi_aclk(clk),
	.s_axi_aresetn(reset), 

	.s_axi_awaddr(m_axi_int_awaddr_inmem),
	.s_axi_awlen(m_axi_int_awlen_inmem),
	.s_axi_awsize(m_axi_int_awsize_inmem),
	.s_axi_awburst(m_axi_int_awburst_inmem),
	.s_axi_awvalid(m_axi_int_awvalid_inmem),
	.s_axi_awready(m_axi_int_awready_inmem),

	// WRITE DATA CHANNEL
	.s_axi_wdata(m_axi_int_wdata_inmem),
	.s_axi_wstrb(m_axi_int_wstrb_inmem),
	.s_axi_wlast(m_axi_int_wlast_inmem),
	.s_axi_wvalid(m_axi_int_wvalid_inmem),
	.s_axi_wready(m_axi_int_wready_inmem),

	// WRITE RESPONSE CHANNEL
	.s_axi_bresp(m_axi_int_bresp_inmem),
	.s_axi_bvalid(m_axi_int_bvalid_inmem),
	.s_axi_bready(m_axi_int_bready_inmem),

	// READ ADDRESS CHANNEL
	.s_axi_araddr(m_axi_int_araddr_inmem),
	.s_axi_arlen(m_axi_int_arlen_inmem),
	.s_axi_arsize(m_axi_int_arsize_inmem),
	.s_axi_arburst(m_axi_int_arburst_inmem),
	.s_axi_arvalid(m_axi_int_arvalid_inmem),
	.s_axi_arready(m_axi_int_arready_inmem),

	// READ DATA CHANNEL
	.s_axi_rdata(m_axi_int_rdata_inmem),
	.s_axi_rresp(m_axi_int_rresp_inmem),
	.s_axi_rlast(m_axi_int_rlast_inmem),
	.s_axi_rvalid(m_axi_int_rvalid_inmem),
	.s_axi_rready(m_axi_int_rready_inmem)
);

bind interconnect slave_axi_cont slave_outmem(
	.s_axi_aclk(clk),
	.s_axi_aresetn(reset), 

	.s_axi_awaddr(m_axi_int_awaddr_outmem),
	.s_axi_awlen(m_axi_int_awlen_outmem),
	.s_axi_awsize(m_axi_int_awsize_outmem),
	.s_axi_awburst(m_axi_int_awburst_outmem),
	.s_axi_awvalid(m_axi_int_awvalid_outmem),
	.s_axi_awready(m_axi_int_awready_outmem),

	// WRITE DATA CHANNEL
	.s_axi_wdata(m_axi_int_wdata_outmem),
	.s_axi_wstrb(m_axi_int_wstrb_outmem),
	.s_axi_wlast(m_axi_int_wlast_outmem),
	.s_axi_wvalid(m_axi_int_wvalid_outmem),
	.s_axi_wready(m_axi_int_wready_outmem),

	// WRITE RESPONSE CHANNEL
	.s_axi_bresp(m_axi_int_bresp_outmem),
	.s_axi_bvalid(m_axi_int_bvalid_outmem),
	.s_axi_bready(m_axi_int_bready_outmem),

	// READ ADDRESS CHANNEL
	.s_axi_araddr(m_axi_int_araddr_outmem),
	.s_axi_arlen(m_axi_int_arlen_outmem),
	.s_axi_arsize(m_axi_int_arsize_outmem),
	.s_axi_arburst(m_axi_int_arburst_outmem),
	.s_axi_arvalid(m_axi_int_arvalid_outmem),
	.s_axi_arready(m_axi_int_arready_outmem),

	// READ DATA CHANNEL
	.s_axi_rdata(m_axi_int_rdata_outmem),
	.s_axi_rresp(m_axi_int_rresp_outmem),
	.s_axi_rlast(m_axi_int_rlast_outmem),
	.s_axi_rvalid(m_axi_int_rvalid_outmem),
	.s_axi_rready(m_axi_int_rready_outmem)
);


bind interconnect slave_axi_cont slave_exreg(
	.s_axi_aclk(clk),
	.s_axi_aresetn(reset), 

	.s_axi_awaddr(m_axi_int_awaddr_exreg),
	.s_axi_awlen(m_axi_int_awlen_exreg),
	.s_axi_awsize(m_axi_int_awsize_exreg),
	.s_axi_awburst(m_axi_int_awburst_exreg),
	.s_axi_awvalid(m_axi_int_awvalid_exreg),
	.s_axi_awready(m_axi_int_awready_exreg),

	// WRITE DATA CHANNEL
	.s_axi_wdata(m_axi_int_wdata_exreg),
	.s_axi_wstrb(m_axi_int_wstrb_exreg),
	.s_axi_wlast(m_axi_int_wlast_exreg),
	.s_axi_wvalid(m_axi_int_wvalid_exreg),
	.s_axi_wready(m_axi_int_wready_exreg),

	// WRITE RESPONSE CHANNEL
	.s_axi_bresp(m_axi_int_bresp_exreg),
	.s_axi_bvalid(m_axi_int_bvalid_exreg),
	.s_axi_bready(m_axi_int_bready_exreg),

	// READ ADDRESS CHANNEL
	.s_axi_araddr(m_axi_int_araddr_exreg),
	.s_axi_arlen(m_axi_int_arlen_exreg),
	.s_axi_arsize(m_axi_int_arsize_exreg),
	.s_axi_arburst(m_axi_int_arburst_exreg),
	.s_axi_arvalid(m_axi_int_arvalid_exreg),
	.s_axi_arready(m_axi_int_arready_exreg),

	// READ DATA CHANNEL
	.s_axi_rdata(m_axi_int_rdata_exreg),
	.s_axi_rresp(m_axi_int_rresp_exreg),
	.s_axi_rlast(m_axi_int_rlast_exreg),
	.s_axi_rvalid(m_axi_int_rvalid_exreg),
	.s_axi_rready(m_axi_int_rready_exreg)
);


bind interconnect slave_axi_cont slave_reg(
	.s_axi_aclk(clk),
	.s_axi_aresetn(reset), 

	.s_axi_awaddr(m_axi_int_awaddr_reg),
	.s_axi_awlen(m_axi_int_awlen_reg),
	.s_axi_awsize(m_axi_int_awsize_reg),
	.s_axi_awburst(m_axi_int_awburst_reg),
	.s_axi_awvalid(m_axi_int_awvalid_reg),
	.s_axi_awready(m_axi_int_awready_reg),

	// WRITE DATA CHANNEL
	.s_axi_wdata(m_axi_int_wdata_reg),
	.s_axi_wstrb(m_axi_int_wstrb_reg),
	.s_axi_wlast(m_axi_int_wlast_reg),
	.s_axi_wvalid(m_axi_int_wvalid_reg),
	.s_axi_wready(m_axi_int_wready_reg),

	// WRITE RESPONSE CHANNEL
	.s_axi_bresp(m_axi_int_bresp_reg),
	.s_axi_bvalid(m_axi_int_bvalid_reg),
	.s_axi_bready(m_axi_int_bready_reg),

	// READ ADDRESS CHANNEL
	.s_axi_araddr(m_axi_int_araddr_reg),
	.s_axi_arlen(m_axi_int_arlen_reg),
	.s_axi_arsize(m_axi_int_arsize_reg),
	.s_axi_arburst(m_axi_int_arburst_reg),
	.s_axi_arvalid(m_axi_int_arvalid_reg),
	.s_axi_arready(m_axi_int_arready_reg),

	// READ DATA CHANNEL
	.s_axi_rdata(m_axi_int_rdata_reg),
	.s_axi_rresp(m_axi_int_rresp_ctreg),
	.s_axi_rlast(m_axi_int_rlast_reg),
	.s_axi_rvalid(m_axi_int_rvalid_reg),
	.s_axi_rready(m_axi_int_rready_reg)
);
////////////////////////////////////////////////////////////////////////////////
// BIND master axi controllers with master checker
////////////////////////////////////////////////////////////////////////////////

bind master_axi_cont checker_master chk_master(
  .clk(m_axi_aclk),
  .reset(m_axi_aresetn),

  .axi_base_address_i(axi_base_address_i),
  .axi_burst_len(axi_burst_len),

  .axi_write_init_i(axi_write_init_i),
  .axi_write_address_i(axi_write_address_i),
  .axi_write_data_i(axi_write_data_i),
  .axi_write_strb_i(axi_write_strb_i),
  .axi_write_vld_i(axi_write_vld_i),
  .axi_write_rdy_o(axi_write_rdy_o),
  .axi_write_done_o(axi_write_done_o),

  .axi_read_init_i(axi_read_init_i),
  .axi_read_address_i(axi_read_address_i),
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
	.reset(rstn),

	.req(req),
	.gnt(gnt),
	.busy(busy)
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
