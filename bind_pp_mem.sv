
bind packet_parser data_memory pp_mem(
  .s_axi_aclk(m_axi_aclk),
  .s_axi_aresetn(m_axi_aresetn),

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

bind packet_parser checker_axi chk_axi_pp(
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

bind packet_parser checker_pp chk_pp(
  .clk(m_axi_aclk),
  .reset(m_axi_aresetn),

  .start_i(start_i),
  .busy_o(busy_o),
  .irq_o(irq_o),
  .addr_hdr_i(addr_hdr_i),
  .ignore_ecc_err_i(ignore_ecc_err_i),
  .pkt_ecc_corr_o(pkt_ecc_corr_o),
  .pkt_ecc_uncorr_o(pkt_ecc_uncorr_o),
  .pkt_crc_err_o(pkt_crc_err_o),
  .pkt_byte_cnt_o(pkt_byte_cnt_o),
  .pkt_type_o(pkt_type_o)
);

bind data_memory checker_inmem chk_inmem(
  .clk(s_axi_aclk),
  .reset(s_axi_aresetn),
  .en_b_i(en_b_i),
  .data_b_i(data_b_i),
  .addr_b_i(addr_b_i),
  .we_b_i(we_b_i),
  .data_b_o(data_b_o)
);
