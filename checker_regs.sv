
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

	start_builder0_task: cover property(pb1_start == 1'b1);


endchecker
