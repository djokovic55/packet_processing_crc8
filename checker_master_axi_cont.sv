checker  checker_master_axi_cont(

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

  reg write_init, read_init;
  reg write_vld;
  logic read_rdy = 1'b1;
  // SECTION Aux code
	

  // NOTE write, read transaction initiation
	always @(posedge clk or posedge reset) begin
		if(reset) begin
			write_init <= 1'b1;
		end
    else if(axi_read_last_o == 1'b1 && write_init == 1'b0) begin
      write_init <= 1'b1;
    end
    else begin
      write_init <= 1'b0;
    end

    if(axi_write_done_o == 1'b1) begin
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
	default disable iff reset;


  //SECTION Properties

  property equal_as_aux_signal(sig_aux, sig);
    sig == sig_aux;
  endproperty

  write_init_gen: assume property (equal_as_aux_signal(write_init, axi_write_init_i));
  read_init_gen: assume property (equal_as_aux_signal(read_init, axi_read_init_i));

  write_vld_gen: assume property (equal_as_aux_signal(write_vld, axi_write_vld_i));
  read_rdy_gen: assume property (equal_as_aux_signal(read_rdy, axi_read_rdy_i));
  endchecker
