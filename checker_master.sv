checker  checker_master(
        clk,
        reset,

        axi_base_address_i,
				axi_burst_len,

        axi_write_init_i,
        axi_write_address_i,
        axi_write_data_i,
        axi_write_strb_i,
        axi_write_vld_i,
        axi_write_rdy_o,
        axi_write_done_o,

        axi_read_init_i,
        axi_read_address_i,
        axi_read_data_o,
        axi_read_vld_o,
        axi_read_rdy_i,
        axi_read_last_o
);

	default 
	clocking @(posedge clk);
	endclocking

	default disable iff reset;

  property stable_address_channel(init, ready, control);
    init |=> $stable(control) s_until ready;
  endproperty

  property equal_as_aux_signal(sig_aux, sig);
    sig == sig_aux;
  endproperty

  logic write_init, read_init;
  logic read_rdy;

	logic read_write_first;
	asm_read_or_write_first: assume property($stable(read_write_first));
	logic write_occured, read_occured;

  enum int unsigned { IDLE = 0, INIT_WRITE = 2, INIT_READ = 4} state, next_state;

  // SECTION Aux code

  always @(posedge clk or posedge reset) begin
		if(reset)
			state <= IDLE;
		else
			state <= next_state;
  end

  always @(state, axi_write_done_o, axi_read_last_o) begin : next_state_logic
      next_state = state;
      case(state)
      IDLE: begin 
				if(!(read_occured || write_occured)) begin
					if(read_write_first)
						next_state = INIT_READ;
					else
						next_state = INIT_WRITE;
					end
				else begin
					next_state = IDLE;
				end
      end
      INIT_WRITE: begin
        if(axi_write_done_o) begin
					write_occured <= 1'b1;
					if(!read_occured)
						next_state = INIT_READ;
					else
						next_state = IDLE;
				end
      end
      INIT_READ: begin
        if(axi_read_last_o) begin
					read_occured <= 1'b1;
					if(!write_occured)
						next_state = INIT_WRITE;
					else
						next_state = IDLE;
				end
      end
      endcase
  end

  always @(state) begin
			// default outputs
			write_init = 1'b0;
			read_init = 1'b0;
			read_rdy = 1'b0;

      case(state)
      IDLE: begin 
        read_rdy = 1'b0;

        write_init = 1'b0;
        read_init = 1'b0;
      end
      INIT_WRITE: begin
        write_init = 1'b1;
      end
      INIT_READ: begin
        read_init = 1'b1;
        read_rdy = 1'b1;
      end
      endcase
  end
  //SECTION Properties

  no_read_and_write: assert property(not(axi_read_init_i && axi_write_init_i));

	asm_write_init_gen: assume property (equal_as_aux_signal(write_init, axi_write_init_i));
  asm_read_init_gen: assume property (equal_as_aux_signal(read_init, axi_read_init_i));

  asm_read_rdy_gen: assume property (equal_as_aux_signal(read_rdy, axi_read_rdy_i));
  // asm_read_rdy_gen: assume property (axi_read_rdy_i == 1'b1);

	asm_base_addr_value: assume property(axi_base_address_i inside {32'h0, 32'h00010000, 32'h00100000, 32'h00200000});
	asm_base_addr_stability: assume property($stable(axi_base_address_i));

	asm_write_addr_stability: assume property($stable(axi_write_address_i));
	asm_write_addr_value: assume property(axi_write_address_i == 32'h7);

	asm_read_addr_stability: assume property($stable(axi_read_address_i));
	asm_read_addr_value: assume property(axi_write_address_i == 32'h7);

	asm_burst_len_max: assume property(axi_burst_len < 8'h5);
	asm_burst_len_stability: assume property($stable(axi_burst_len));
	asm_data_stability: assume property($stable(axi_write_data_i));
	asm_wstrb_stability: assume property($stable(axi_write_strb_i));
	


	//Section cover
  // read_last_c: cover property(axi_read_last_o);
	// write_done: cover property(axi_write_done_o);
	// read_init_gen_c: cover property(axi_read_init_i);
	// read_init_aux_gen_c: cover property(read_init);
	

  endchecker
