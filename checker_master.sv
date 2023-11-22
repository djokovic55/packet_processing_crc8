
checker  checker_master(

        clk,
        reset,

        axi_base_address_i,
        axi_write_address_i,
        // init write
        axi_write_init_i,
        axi_write_data_i,
        axi_write_vld_i,
        axi_write_rdy_o,
        // finish write
        axi_write_done_o,

        axi_read_address_i,
        axi_read_init_i,
        axi_read_data_o,
        axi_read_vld_o,
        axi_read_rdy_i,
        axi_read_last_o
	////////////////////////////////////////////////////////////////////////////////

);

	default 
	clocking @(posedge clk);
	endclocking

	default disable iff reset;

  // logic write_init, read_init;
  // logic write_vld;
  // logic read_rdy;

  // enum int unsigned { IDLE = 0, INIT_WRITE = 2, INIT_READ = 4} state, next_state;

  // // SECTION Aux code

  // always @(posedge clk or posedge reset) begin
  //     if(reset)
  //     state <= IDLE;
  //     else
  //     state <= next_state;
  // end

  // always @(state, axi_write_done_o, axi_read_last_o) begin : next_state_logic
  //     next_state = state;
  //     case(state)
  //     IDLE: begin 
  //         next_state = INIT_WRITE;

  //     end
  //     INIT_WRITE: begin
  //       if(axi_write_done_o)
  //         next_state = INIT_READ;

  //     end
  //     INIT_READ: begin
  //       if(axi_read_last_o)
  //         next_state = IDLE;
  //     end
  //     endcase
  // end

  // always @(state) begin

	// 		// default outputs
	// 		write_init = 1'b0;
	// 		read_init = 1'b0;
	// 		write_vld = 1'b0;
	// 		read_rdy = 1'b0;

  //     case(state)
  //     IDLE: begin 
  //       write_vld = 1'b0;
  //       read_rdy = 1'b0;

  //       write_init = 1'b0;
  //       read_init = 1'b0;
  //     end
  //     INIT_WRITE: begin
  //       write_init = 1'b1;
  //       write_vld = 1'b1;
  //     end
  //     INIT_READ: begin
  //       read_init = 1'b1;
  //       read_rdy = 1'b1;
  //     end
  //     endcase
  // end


  //SECTION Properties

  property equal_as_aux_signal(sig_aux, sig);
    sig == sig_aux;
  endproperty

  no_read_and_write: assume property(not(write_init && read_init));
  asm_read_rdy: assume property(axi_read_rdy_i == 1'b1)
  
  // write_base_address: assume property(axi_base_address_i == 32'h00000000);
  // write_address: assume property(axi_write_address_i == 32'h000000FF);
  // read_address: assume property(axi_read_address_i == 32'h000000FF);


  // stable_read_base_addr: assume property(stable_before_handshake(read_init, axi_read_last_o, axi_base_address_i));
  // stable_read_addr: assume property(stable_before_handshake(read_init, axi_read_last_o, axi_read_address_i));

  // stable_write_base_addr: assume property(stable_before_handshake(write_init, axi_write_done_o, axi_base_address_i));
  // stable_write_addr: assume property(stable_before_handshake(write_init, axi_write_done_o, axi_write_address_i));

  // write_init_gen: assume property (equal_as_aux_signal(write_init, axi_write_init_i));
  // read_init_gen: assume property (equal_as_aux_signal(read_init, axi_read_init_i));

  // write_vld_gen: assume property (equal_as_aux_signal(write_vld, axi_write_vld_i));
  // read_rdy_gen: assume property (equal_as_aux_signal(read_rdy, axi_read_rdy_i));

	//Section cover
  // read_last_c: cover property(axi_read_last_o);
	// write_done: cover property(axi_write_done_o);
	// read_init_gen_c: cover property(axi_read_init_i);
	// read_init_aux_gen_c: cover property(read_init);
	

  endchecker