
checker checker_inmem(
  clk,
  reset,

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

endchecker
