bind packet_builder checker_pb chk_pb(
  .clk(m_axi_aclk),
  .reset(m_axi_aresetn),

  .start_i(start_i),
  .busy_o(busy_o),
  .irq_o(irq_o),
  .addr_in_i(addr_in_i),
  .byte_cnt_i(byte_cnt_i),
  .pkt_type_i(pkt_type_i),
  .ecc_en_i(ecc_en_i),
  .crc_en_i(crc_en_i),
  .ins_ecc_err_i(ins_ecc_err_i),
  .ins_crc_err_i(ins_crc_err_i),
  .ecc_val_i(ecc_val_i),
  .crc_val_i(crc_val_i),
  .sop_val_i(sop_val_i),
  .data_sel_i(data_sel_i),
  .addr_out_i(addr_out_i),

  .s_axi_awaddr(m_axi_awaddr),
  .s_axi_awlen(m_axi_awlen),
  .s_axi_awsize(m_axi_awsize),
  .s_axi_awburst(m_axi_awburst),
  .s_axi_awvalid(m_axi_awvalid),
  .s_axi_awready(m_axi_awready),

  .s_axi_wdata(m_axi_wdata),
  .s_axi_wstrb(m_axi_wstrb),
  .s_axi_wlast(m_axi_wlast),
  .s_axi_wvalid(m_axi_wvalid),
  .s_axi_wready(m_axi_wready),

  .s_axi_bresp(m_axi_bresp),
  .s_axi_bvalid(m_axi_bvalid),
  .s_axi_bready(m_axi_bready),
  
  .s_axi_araddr(m_axi_araddr),
  .s_axi_arlen(m_axi_arlen),
  .s_axi_arsize(m_axi_arsize),
  .s_axi_arburst(m_axi_arburst),
  .s_axi_arvalid(m_axi_arvalid),
  .s_axi_arready(m_axi_arready),

  .s_axi_rdata(m_axi_rdata),
  .s_axi_rresp(m_axi_rresp),
  .s_axi_rlast(m_axi_rlast),
  .s_axi_rvalid(m_axi_rvalid),
  .s_axi_rready(m_axi_rready)

);

bind packet_builder checker_axi chk_axi_pb(
	.clk(m_axi_aclk),
	.reset(m_axi_aresetn), 

	.awaddr(m_axi_awaddr),
	.awlen(m_axi_awlen),
	.awsize(m_axi_awsize),
	.awburst(m_axi_awburst),
	.awvalid(m_axi_awvalid),
	.awready(m_axi_awready),

	.wdata(m_axi_wdata),
	.wstrb(m_axi_wstrb),
	.wlast(m_axi_wlast),
	.wvalid(m_axi_wvalid),
	.wready(m_axi_wready),

	.bresp(m_axi_bresp),
	.bvalid(m_axi_bvalid),
	.bready(m_axi_bready),

	.araddr(m_axi_araddr),
	.arlen(m_axi_arlen),
	.arsize(m_axi_arsize),
	.arburst(m_axi_arburst),
	.arvalid(m_axi_arvalid),
	.arready(m_axi_arready),

	.rdata(m_axi_rdata),
	.rresp(m_axi_rresp),
	.rlast(m_axi_rlast),
	.rvalid(m_axi_rvalid),
	.rready(m_axi_rready)
);

bind packet_builder checker_sb chk_sb(
  .clk(m_axi_aclk),
  .reset(m_axi_aresetn),

  .byte_cnt(byte_cnt_i),
  .data_sel(data_sel_i),

  .wdata(m_axi_wdata),
  .wvalid(m_axi_wvalid),
  .wlast(m_axi_wlast),
  .wready(m_axi_wready), 

  .rdata(m_axi_rdata),
  .rlast(m_axi_rlast),
  .rvalid(m_axi_rvalid),
  .rready(m_axi_rready)
);


