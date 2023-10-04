
bind top checker_top_ex_regs chk_top_ex_regs(
	.clk(clk),
	.reset(reset),

	.pb_irq(pb_irq_i),
	.pb_addr_in(pb_addr_in_i),
	.pb_byte_cnt(pb_byte_cnt_i),
	.pb_pkt_type(pb_pkt_type_i),
	.pb_ecc_en(pb_ecc_en_i),
	.pb_crc_en(pb_crc_en_i),
	.pb_ins_ecc_err(pb_ins_ecc_err_i),
	.pb_ins_crc_err(pb_ins_crc_err_i),
	.pb_ecc_val(pb_ecc_val_i),
	.pb_crc_val(pb_crc_val_i),
	.pb_sop_val(pb_sop_val_i),
	.pb_data_sel(pb_data_sel_i),
	.pb_addr_out(pb_addr_out_i),

	.pp_irq(pp_irq_i),
	.pp_addr_hdr(pp_addr_hdr_i),
	.pp_ignore_ecc_err(pp_ignore_ecc_err_i)
);


bind top.system_regs checker_regs chk_regs(

	.clk(S_AXI_ACLK),
	.reset(S_AXI_ARESETN),

	.int_irq(int_irq_o),

	.pb0_start(pb0_start_o),
	.pb0_busy(pb0_busy_i),
	.pb0_irq(pb0_irq_i),
	.pb0_addr_in(pb0_addr_in_o),
	.pb0_byte_cnt(pb0_byte_cnt_o),
	.pb0_pkt_type(pb0_pkt_type_o),
	.pb0_ecc_en(pb0_ecc_en_o),
	.pb0_crc_en(pb0_crc_en_o),
	.pb0_ins_ecc_err(pb0_ins_ecc_err_o),
	.pb0_ins_crc_err(pb0_ins_crc_err_o),
	.pb0_ecc_val(pb0_ecc_val_o),
	.pb0_crc_val(pb0_crc_val_o),
	.pb0_sop_val(pb0_sop_val_o),
	.pb0_data_sel(pb0_data_sel_o),
	.pb0_addr_out(pb0_addr_out_o),

	 // [x] interface with builder1
	.pb1_start(pb1_start_o),
	.pb1_busy(pb1_busy_i),
	.pb1_irq(pb1_irq_i),
	.pb1_addr_in(pb1_addr_in_o),
	.pb1_byte_cnt(pb1_byte_cnt_o),
	.pb1_pkt_type(pb1_pkt_type_o),
	.pb1_ecc_en(pb1_ecc_en_o),
	.pb1_crc_en(pb1_crc_en_o),
	.pb1_ins_ecc_err(pb1_ins_ecc_err_o),
	.pb1_ins_crc_err(pb1_ins_crc_err_o),
	.pb1_ecc_val(pb1_ecc_val_o),
	.pb1_crc_val(pb1_crc_val_o),
	.pb1_sop_val(pb1_sop_val_o),
	.pb1_data_sel(pb1_data_sel_o),
	.pb1_addr_out(pb1_addr_out_o),
	// [x] interface with parser

	.pp_start(pp_start_o),
	.pp_busy(pp_busy_i),
	.pp_irq(pp_irq_i),
	.pp_addr_hdr(pp_addr_hdr_o),
	.pp_ignore_ecc_err(pp_ignore_ecc_err_o),
	.pp_pkt_ecc_corr(pp_pkt_ecc_corr_i),
	.pp_pkt_ecc_uncorr(pp_pkt_ecc_uncorr_i),
	.pp_pkt_crc_err(pp_pkt_crc_err_i),
	.pp_pkt_byte_cnt(pp_pkt_byte_cnt_i),
	.pp_pkt_type(pp_pkt_type_i)

);

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
