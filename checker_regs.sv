
checker  checker_regs(
	clk	,
	reset	,

  int_irq,

  // [x] interface with builder0
  pb0_start,
  pb0_busy,
  pb0_irq,
  pb0_addr_in,
  pb0_byte_cnt,
  pb0_pkt_type,
  pb0_ecc_en,
  pb0_crc_en,
  pb0_ins_ecc_err,
  pb0_ins_crc_err,
  pb0_ecc_val,
  pb0_crc_val,
  pb0_sop_val,
  pb0_data_sel,
  pb0_addr_out,

  // [x] interface with builder1
  pb1_start,
  pb1_busy,
  pb1_irq,
  pb1_addr_in,
  pb1_byte_cnt,
  pb1_pkt_type,
  pb1_ecc_en,
  pb1_crc_en,
  pb1_ins_ecc_err,
  pb1_ins_crc_err,
  pb1_ecc_val,
  pb1_crc_val,
  pb1_sop_val,
  pb1_data_sel,
  pb1_addr_out,

  // [x] interface with parser
  pp_start,
  pp_busy,
  pp_irq,
  pp_addr_hdr,
  pp_ignore_ecc_err,
  pp_pkt_ecc_corr,
  pp_pkt_ecc_uncorr,
  pp_pkt_crc_err,
  pp_pkt_byte_cnt,
  pp_pkt_type

);

	default clocking @(posedge clk);
	endclocking

	default disable iff reset;
	////////////////////////////////////////////////////////////////////////////////
	// Packet builder 0 properties
	////////////////////////////////////////////////////////////////////////////////
	pb0_start_c: cover property(pb0_start == 1'b1);
	pb0_in_addr_c: cover property(pb0_addr_in == 32'hFFFF0000);

  pb0_byte_cnt_c: cover property(pb0_byte_cnt == 4'b1111);
  pb0_pkt_type_c: cover property(pb0_pkt_type == 4'b1000);
  pb0_ecc_en_c: cover property(pb0_ecc_en == 1'b1);
  pb0_crc_en_c: cover property(pb0_crc_en == 1'b1);
  pb0_ins_ecc_err_c: cover property(pb0_ins_ecc_err == 2'b00);
  pb0_ins_crc_err_c: cover property(pb0_ins_crc_err == 1'b0);
  pb0_ecc_val_c: cover property(pb0_ecc_val == 4'b1010);
  pb0_crc_val_c: cover property(pb0_crc_val == 7'b1000000);
  pb0_sop_val_c: cover property(pb0_sop_val == 4'b1111);
  pb0_data_sel_c: cover property(pb0_data_sel == 4'b0010);

  pb0_addr_out_c: cover property(pb0_addr_out == 32'h0000FFFF);

	////////////////////////////////////////////////////////////////////////////////
	// Packet builder 1 properties
	////////////////////////////////////////////////////////////////////////////////
	pb1_start_c: cover property(pb1_start == 1'b1);
	pb1_in_addr_c: cover property(pb1_addr_in == 32'hFFFF0000);

  pb1_byte_cnt_c: cover property(pb1_byte_cnt == 4'b1111);
  pb1_pkt_type_c: cover property(pb1_pkt_type == 4'b1000);
  pb1_ecc_en_c: cover property(pb1_ecc_en == 1'b1);
  pb1_crc_en_c: cover property(pb1_crc_en == 1'b1);
  pb1_ins_ecc_err_c: cover property(pb1_ins_ecc_err == 2'b00);
  pb1_ins_crc_err_c: cover property(pb1_ins_crc_err == 1'b0);
  pb1_ecc_val_c: cover property(pb1_ecc_val == 4'b1010);
  pb1_crc_val_c: cover property(pb1_crc_val == 7'b1000000);
  pb1_sop_val_c: cover property(pb1_sop_val == 4'b1111);
  pb1_data_sel_c: cover property(pb1_data_sel == 4'b0010);

  pb1_addr_out_c: cover property(pb1_addr_out == 32'h0000FFFF);

	////////////////////////////////////////////////////////////////////////////////
	// Packet parser properties
	////////////////////////////////////////////////////////////////////////////////
  pp_start_c: cover property(pp_start == 1'b1);
  pp_addr_hdr_c: cover property(pp_addr_hdr == 32'hAAAA0000);
  pp_ignore_ecc_err_c: cover property(pp_ignore_ecc_err == 1'b1);


endchecker
