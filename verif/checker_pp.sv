
checker checker_pp(
	clk,
	reset,

	start_i,
	busy_o,
	irq_o,
	addr_hdr_i,
	ignore_ecc_err_i,
	pkt_ecc_corr_o,
	pkt_ecc_uncorr_o,
	pkt_crc_err_o,
	pkt_byte_cnt_o,
	pkt_type_o
);

	default clocking @(posedge clk);
	endclocking

	default disable iff reset;

  property aux_eq(sig, sig_aux);
    sig == sig_aux;
  endproperty

  // asm_addr_hdr_i: assume property (addr_hdr_i == 32'hf);
  asm_ignore_ecc_err: assume property (ignore_ecc_err_i == 1'b0);

  //SECTION Check and cover
  cov_pp_start: cover property(start_i == 1'b1);
  cov_ecc_corr_err: cover property(pkt_ecc_corr_o == 1'b1);
  cov_ecc_uncorr_err: cover property(pkt_ecc_uncorr_o == 1'b1);

endchecker
