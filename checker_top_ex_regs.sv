
checker  checker_top_ex_regs(
	clk	,
	reset	,

  pb_irq,
  pb_addr_in,
  pb_byte_cnt,
  pb_pkt_type,
  pb_ecc_en,
  pb_crc_en,
  pb_ins_ecc_err,
  pb_ins_crc_err,
  pb_ecc_val,
  pb_crc_val,
  pb_sop_val,
  pb_data_sel,
  pb_addr_out,

  pp_irq,
  pp_addr_hdr,
  pp_ignore_ecc_err

);

	default 
	clocking @(posedge clk);
	endclocking

	default disable iff reset;

	//SECTION Constraints
	max_byte_cnt: assume property(pb_byte_cnt == 4'h8 );
	merging_option: assume property(pb_data_sel == 4'h0);
	crc_en: assume property(pb_crc_en == 1'b1);
	ecc_en: assume property(pb_ecc_en == 1'b1);
	

	//SECTION Cover
	pb_irq_c: cover property(pb_irq[*5]);
	pp_irq_c: cover property(pp_irq[*5]);


endchecker
