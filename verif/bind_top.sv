
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
  .pp_ignore_ecc_err(pp_ignore_ecc_err_i),

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

	// cont top stutus
	.cont_busy_top(cont_busy_top),

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
  .pp_pkt_type_top(pp_pkt_type_top)
);

// bind top.subsys checker_data_integrity chk_data_integrity(
//   .clk(clk),	
//   .reset(reset),
//   .byte_cnt(pb_byte_cnt_i),
//   .data_sel(pb_data_sel_i),

//   .wdata(m_axi_int_wdata_outmem),
//   .wvalid(m_axi_int_wvalid_outmem),
//   .wlast(m_axi_int_wlast_outmem),
//   .wready(m_axi_int_wready_outmem), 

//   .rdata(m_axi_int_rdata_inmem),
//   .rlast(m_axi_int_rlast_inmem),
//   .rvalid(m_axi_int_rvalid_inmem),
//   .rready(m_axi_int_rready_inmem)
// );

bind top.subsys.packet_builder0 checker_data_integrity chk_data_integrity(
  .clk(M_AXI_ACLK),	
  .reset(M_AXI_ARESETN),
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

bind top.subsys.intcon.arb_inst checker_fair_int chk_fairness(
  .clk(clk),
  .reset(rstn),

  .req(req),
  .gnt(gnt),
  .busy(busy)
);
////////////////////////////////////////////////////////////////////////////////
// BIND axi controllers with axi protocol checker
////////////////////////////////////////////////////////////////////////////////

bind top.subsys.intcon checker_axi chk_axi_prot_ctrl(
  .clk(clk),
  .reset(reset), 

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

bind top.subsys.intcon checker_axi chk_axi_prot_pb0(
  .clk(clk),
  .reset(reset), 

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

bind top.subsys.intcon checker_axi chk_axi_prot_pb1(
  .clk(clk),
  .reset(reset), 

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

bind top.subsys.intcon checker_axi chk_axi_prot_pp(
  .clk(clk),
  .reset(reset), 

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

bind top.subsys.intcon checker_axi chk_axi_prot_inmem(
  .clk(clk),
  .reset(reset), 

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

bind top.subsys.intcon checker_axi chk_axi_prot_outmem(
  .clk(clk),
  .reset(reset), 

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

bind top.subsys.intcon checker_axi chk_axi_prot_reg(
  .clk(clk),
  .reset(reset), 

  .awaddr(m_axi_int_awaddr_reg),
  .awlen(m_axi_int_awlen_reg),
  .awsize(m_axi_int_awsize_reg),
  .awburst(m_axi_int_awburst_reg),
  .awvalid(m_axi_int_awvalid_reg),
  .awready(m_axi_int_awready_reg),

  // WRITE DATA CHANNEL
  .wdata(m_axi_int_wdata_reg),
  .wstrb(m_axi_int_wstrb_reg),
  .wlast(m_axi_int_wlast_reg),
  .wvalid(m_axi_int_wvalid_reg),
  .wready(m_axi_int_wready_reg),

  // WRITE RESPONSE CHANNEL
  .bresp(m_axi_int_bresp_reg),
  .bvalid(m_axi_int_bvalid_reg),
  .bready(m_axi_int_bready_reg),

  // READ ADDRESS CHANNEL
  .araddr(m_axi_int_araddr_reg),
  .arlen(m_axi_int_arlen_reg),
  .arsize(m_axi_int_arsize_reg),
  .arburst(m_axi_int_arburst_reg),
  .arvalid(m_axi_int_arvalid_reg),
  .arready(m_axi_int_arready_reg),

  // READ DATA CHANNEL
  .rdata(m_axi_int_rdata_reg),
  .rresp(m_axi_int_rresp_reg),
  .rlast(m_axi_int_rlast_reg),
  .rvalid(m_axi_int_rvalid_reg),
  .rready(m_axi_int_rready_reg)
  ////////////////////////////////////////////////////////////////////////////////
);

bind top.subsys.intcon checker_axi chk_axi_prot_exreg(
  .clk(clk),
  .reset(reset), 

  .awaddr(m_axi_int_awaddr_exreg),
  .awlen(m_axi_int_awlen_exreg),
  .awsize(m_axi_int_awsize_exreg),
  .awburst(m_axi_int_awburst_exreg),
  .awvalid(m_axi_int_awvalid_exreg),
  .awready(m_axi_int_awready_exreg),

  // WRITE DATA CHANNEL
  .wdata(m_axi_int_wdata_exreg),
  .wstrb(m_axi_int_wstrb_exreg),
  .wlast(m_axi_int_wlast_exreg),
  .wvalid(m_axi_int_wvalid_exreg),
  .wready(m_axi_int_wready_exreg),

  // WRITE RESPONSE CHANNEL
  .bresp(m_axi_int_bresp_exreg),
  .bvalid(m_axi_int_bvalid_exreg),
  .bready(m_axi_int_bready_exreg),

  // READ ADDRESS CHANNEL
  .araddr(m_axi_int_araddr_exreg),
  .arlen(m_axi_int_arlen_exreg),
  .arsize(m_axi_int_arsize_exreg),
  .arburst(m_axi_int_arburst_exreg),
  .arvalid(m_axi_int_arvalid_exreg),
  .arready(m_axi_int_arready_exreg),

  // READ DATA CHANNEL
  .rdata(m_axi_int_rdata_exreg),
  .rresp(m_axi_int_rresp_exreg),
  .rlast(m_axi_int_rlast_exreg),
  .rvalid(m_axi_int_rvalid_exreg),
  .rready(m_axi_int_rready_exreg)
  ////////////////////////////////////////////////////////////////////////////////
);
