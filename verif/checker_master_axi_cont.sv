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
        axi_read_last_o,

	awaddr,
	awlen,
	awsize,
	awburst,
	awvalid,
	awready,

	// WRITE DATA CHANNEL
	wdata,
	wstrb,
	wlast,
	wvalid,
	wready,

	// WRITE RESPONSE CHANNEL
	bresp,
	bvalid,
	bready,

	// READ ADDRESS CHANNEL
	araddr,
	arlen,
	arsize,
	arburst,
	arvalid,
	arready,

	// READ DATA CHANNEL
	rdata,
	rresp,
	rlast,
	rvalid,
	rready
	////////////////////////////////////////////////////////////////////////////////

);

	default 
	clocking @(posedge clk);
	endclocking

	default disable iff reset;

	read_init_c: cover property(axi_read_init_i);
	rvalid_c: cover property(axi_read_init_i ##[0:1] arvalid);


  endchecker
