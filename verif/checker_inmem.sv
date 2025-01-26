
checker checker_inmem(
  clk,
  reset,

  en_a_i,
  data_a_i,
  addr_a_i,
  we_a_i,
  data_a_o,

  // memory port B interface
  en_b_i,
  data_b_i,
  addr_b_i,
  we_b_i,
  data_b_o

);

	default clocking @(posedge clk);
	endclocking

	default disable iff reset;

  property aux_eq(sig, sig_aux);
    sig == sig_aux;
  endproperty

	// asm_bram_pb_test: assume property(data_b_i == 32'hBEEFBABA);
	cov_web: cover property(we_b_i == 1'b1);
	cov_mem_read: cover property(data_a_o == 32'hFEEDBABA && addr_a_i == 14'h7);

endchecker
