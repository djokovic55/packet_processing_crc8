
bind top checker_top chk_top(
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

  // inmem port B top interface, used for memory configuration
  .inmem_en_b_i(inmem_en_b_i),
  .inmem_data_b_i(inmem_data_b_i),
  .inmem_addr_b_i(inmem_addr_b_i),
  .inmem_we_b_i(inmem_we_b_i),
  .inmem_data_b_o(inmem_data_b_o),

  // outmem port B top interface, memory read only
  .outmem_en_b_i(outmem_en_b_i),
  .outmem_data_b_i(outmem_data_b_i),
  .outmem_addr_b_i(outmem_addr_b_i),
  .outmem_we_b_i(outmem_we_b_i),
  .outmem_data_b_o(outmem_data_b_o),

  // regs top interface
  .pb0_start_top(pb0_start_top),
  .pb0_busy_top(pb0_busy_top),
  .pb0_irq_top(pb0_irq_top),
  .pb0_addr_in_top(pb0_addr_in_top),
  .pb0_byte_cnt_top(pb0_byte_cnt_top),
  .pb0_pkt_type_top(pb0_pkt_type_top),
  .pb0_ecc_en_top(pb0_ecc_en_top),
  .pb0_crc_en_top(pb0_crc_en_top),
  .pb0_ins_ecc_err_top(pb0_ins_ecc_err_top),
  .pb0_ins_crc_err_top(pb0_ins_crc_err_top),
  .pb0_ecc_val_top(pb0_ecc_val_top),
  .pb0_crc_val_top(pb0_crc_val_top),
  .pb0_sop_val_top(pb0_sop_val_top),
  .pb0_data_sel_top(pb0_data_sel_top),
  .pb0_addr_out_top(pb0_addr_out_top),
  .pb1_start_top(pb1_start_top),
  .pb1_busy_top(pb1_busy_top),
  .pb1_irq_top(pb1_irq_top),
  .pb1_addr_in_top(pb1_addr_in_top),
  .pb1_byte_cnt_top(pb1_byte_cnt_top),
  .pb1_pkt_type_top(pb1_pkt_type_top),
  .pb1_ecc_en_top(pb1_ecc_en_top),
  .pb1_crc_en_top(pb1_crc_en_top),
  .pb1_ins_ecc_err_top(pb1_ins_ecc_err_top),
  .pb1_ins_crc_err_top(pb1_ins_crc_err_top),
  .pb1_ecc_val_top(pb1_ecc_val_top),
  .pb1_crc_val_top(pb1_crc_val_top),
  .pb1_sop_val_top(pb1_sop_val_top),
  .pb1_data_sel_top(pb1_data_sel_top),
  .pb1_addr_out_top(pb1_addr_out_top),
  .pp_start_top(pp_start_top),
  .pp_busy_top(pp_busy_top),
  .pp_irq_top(pp_irq_top),
  .pp_addr_hdr_top(pp_addr_hdr_top),
  .pp_ignore_ecc_err_top(pp_ignore_ecc_err_top),
  .pp_pkt_ecc_corr_top(pp_pkt_ecc_corr_top),
  .pp_pkt_ecc_uncorr_top(pp_pkt_ecc_uncorr_top),
  .pp_pkt_crc_err_top(pp_pkt_crc_err_top),
  .pp_pkt_byte_cnt_top(pp_pkt_byte_cnt_top),
  .pp_pkt_type_top(pp_pkt_type_top),
);

bind top.top_subsystem checker_data_integrity chk_data_integrity(
	.clk(clk),	
	.reset(reset),
	.byte_cnt(pb_byte_cnt_i),
	.data_sel(pb_data_sel_i),

	.wdata(m_axi_int_wdata_outmem),
	.wvalid(m_axi_int_wvalid_outmem),
	.wlast(m_axi_int_wlast_outmem),
	.wready(m_axi_int_wready_outmem), 

	.rdata(m_axi_int_rdata_inmem),
	.rlast(m_axi_int_rlast_inmem),
	.rvalid(m_axi_int_rvalid_inmem),
	.rready(m_axi_int_rready_inmem)
);


bind top.top_subsystem.interconnect.arbiter_rr checker_fair_int chk_fairness(
	.clk(clk),
	.reset(rstn),

	.req(req),
	.gnt(gnt),
	.busy(busy)
);
////////////////////////////////////////////////////////////////////////////////
// BIND axi controllers with axi protocol checker
////////////////////////////////////////////////////////////////////////////////

bind top.top_subsystem.interconnect checker_axi chk_axi_prot(
	.clk(m_axi_aclk),
	.reset(m_axi_aresetn), 

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