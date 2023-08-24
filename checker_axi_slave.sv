
checker  checker_axi_slave(
	clk	,
	reset	,

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
	
	// NOTE Write transaction

	awvalid_c: cover property(awvalid);
	awready_c: cover property(awready);

	wvalid_c: cover property(wvalid);
	wready_c: cover property(wready);
	wvalid_and_wready_c: cover property(wvalid && wready);

	// NOTE Read transaction

	// slave_gen_rlast_c: cover property(rlast);
	// axi_arlen_cntr_c: cover property();
	arvalid_c: cover property(arvalid);
	// arready_c: cover property(arready);
	// arvalid_and_not_arready_c: cover property(arvalid && !arready);

	rvalid_c: cover property(rvalid);
	rready_c: cover property(rready);
	rvalid_and_rready_c: cover property(rvalid && rready);










endchecker



