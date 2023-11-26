
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

bind top.packet_builder0 checker_data_integrity chk_data_integrity(
	.clk(clk),	
	.reset(reset),
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

// checker_axi to added