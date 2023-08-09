
checker  checker_top(

        clk,
        reset,

        axi_base_address_i,
        axi_write_address_i,
        axi_write_init_i,
        axi_write_data_i,
        axi_write_vld_i,
        axi_write_rdy_o,
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

  reg write_init, read_init;
  reg write_vld;
  logic read_rdy;
  // SECTION Aux code
	

  // BUG Design overconstrained

  // NOTE write, read transaction initiation
	always @(posedge clk or posedge reset) begin
		if(reset) begin
			write_init <= 1'b1;
		end
    else if(axi_read_last_o == 1'b1 && write_init == 1'b0 && !read_init) begin
      write_init <= 1'b1;
    end
    else begin
      write_init <= 1'b0;
    end

    if(axi_write_done_o == 1'b1 && !write_init) begin
      read_init <= 1'b1;
    end
    else if(read_init == 1'b1) begin
      read_init <= 1'b0;
    end

	end



	always @(posedge clk or posedge reset) begin
		if(reset || axi_write_done_o) begin
      write_vld <= 1'b0;
    end
    else if(write_init == 1'b1) begin 
      write_vld <= 1'b1;
    end
  end

  //SECTION Properties

  property stable_before_handshake(valid, ready, control);
    valid && !ready |=> $stable(control);
  endproperty

  property equal_as_aux_signal(sig_aux, sig);
    sig == sig_aux;
  endproperty

  no_read_and_write: assert property(not(write_init && read_init));
  
  write_base_address: assume property(axi_base_address_i == 32'h00000000);
  write_address: assume property(axi_write_address_i == 32'h000000FF);
  read_address: assume property(axi_read_address_i == 32'h000000FF);


  // stable_read_base_addr: assume property(stable_before_handshake(read_init, axi_read_last_o, axi_base_address_i));
  // stable_read_addr: assume property(stable_before_handshake(read_init, axi_read_last_o, axi_read_address_i));

  // stable_write_base_addr: assume property(stable_before_handshake(write_init, axi_write_done_o, axi_base_address_i));
  // stable_write_addr: assume property(stable_before_handshake(write_init, axi_write_done_o, axi_write_address_i));

  write_init_gen: assume property (equal_as_aux_signal(write_init, axi_write_init_i));
  read_init_gen: assume property (equal_as_aux_signal(read_init, axi_read_init_i));

  write_vld_gen: assume property (equal_as_aux_signal(write_vld, axi_write_vld_i));
  read_rdy_gen: assume property (equal_as_aux_signal(read_rdy, axi_read_rdy_i));

	//Section cover
  read_last_c: cover property(axi_read_last_o);

	write_done: cover property(axi_write_done_o);
	read_init_gen_c: cover property(axi_read_init_i);
	

  endchecker
