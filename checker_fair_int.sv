
checker checker_fair_int(
  clk,
  reset,

  req,
  gnt,
	busy
);

	default clocking @(posedge clk);
	endclocking

	default disable iff reset;

  property aux_eq(sig, sig_aux);
    sig == sig_aux;
  endproperty

  logic[1:0] chosen_agent_a;
  logic[1:0] chosen_agent_b;

  asm_agent_a_stability: assume property ($stable(chosen_agent_a));
  asm_agent_b_stability: assume property ($stable(chosen_agent_b));

  logic agent_b_should_be_granted;
  always @(posedge clk)
    if(reset) 
      agent_b_should_be_granted <= 1'b0;
    else begin
      if(gnt[chosen_agent_b] && !busy)
        agent_b_should_be_granted <= 1'b0;
      else if(req[chosen_agent_b] && gnt[chosen_agent_a] && !busy)
        agent_b_should_be_granted <= 1'b1;
    end

  ast_fairness: assert property(gnt[chosen_agent_a] |-> !agent_b_should_be_granted);
  ast_no_deadlock: assert property(not(busy[*20]));
endchecker
