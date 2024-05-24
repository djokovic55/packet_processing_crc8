
checker  checker_axi(
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

	reg [4 : 0] handshake_cnt_w, handshake_cnt_r;

	//SECTION Aux code

	always @(posedge clk) begin
		if(reset) begin
			handshake_cnt_w <= 1'b0;
		end
		else begin
			if(wvalid && wready && !wlast && awlen != '0) begin
				handshake_cnt_w <= handshake_cnt_w + 1'b1;
			end
			else if(wlast) begin
				handshake_cnt_w <= 1'b0;
			end
		end
	end

	always @(posedge clk or posedge reset) begin
		if(reset) begin
			handshake_cnt_r <= 1'b0;
		end
		else begin
			if(rvalid && rready && !rlast && arlen != '0) begin
				handshake_cnt_r <= handshake_cnt_r + 1'b1;
			end
			else if(rlast) begin
				handshake_cnt_r <= 1'b0;
			end
		end
	end

		// FIXME Stability properties cannot be proven until ready logic is implemented
  // SECTION Property definitions

  //NOTE Assert
  property ast_axi_stable_before_handshake(valid, ready, control);
    valid && !ready |=> $stable(control);
  endproperty

  property ast_axi_valid_before_handshake(valid, ready);
    valid && !ready |=> valid;
  endproperty

  property handshake_max_wait(valid, ready, timeout);
    valid && !ready |-> ##[0:timeout] ready;
  endproperty

  property ast_axi_data_last (handshake_cnt, axlen, xlast);
		(handshake_cnt == axlen) && (axlen != '0) |-> xlast;
  endproperty

  property ast_axi_single_burst_data_last (axlen, xlast, axready, axvalid);
		axready && axvalid && (axlen == '0) |=> xlast;
  endproperty

  property ast_axi_single_burst_data_last_stable (xlast, xready, xvalid);
		xlast && (!xready || !xvalid) |=> xlast;
  endproperty

  property ast_axi_size (axvalid, axsize);
		axvalid |-> axsize == 2;
  endproperty

  property ast_axi_resp (xresp, xvalid);
		xvalid |-> xresp == 0;
  endproperty

  //FIXME awready prop are not defined

  //NOTE Cover
  property valid_before_ready(valid, ready);
    valid && !ready;
  endproperty

  property ready_before_valid(valid, ready);
    !valid && ready;
  endproperty

  property valid_with_ready(valid, ready);
    valid && ready;
  endproperty


  //SECTION AW channel prop

  ast_axi_aw_stable_awaddr: assert property (ast_axi_stable_before_handshake(awvalid, awready, awaddr));
  ast_axi_aw_stable_awlen: assert property (ast_axi_stable_before_handshake(awvalid, awready, awlen));
  ast_axi_aw_stable_awsize: assert property (ast_axi_stable_before_handshake(awvalid, awready, awsize));
  ast_axi_aw_stable_awburst: assert property (ast_axi_stable_before_handshake(awvalid, awready, awburst));
  ast_axi_aw_awvalid_until_awready: assert property (ast_axi_valid_before_handshake(awvalid, awready));

	ast_axi_aw_valid_awsize: assert property(ast_axi_size(awvalid, awsize));
  // ast_awready_max_wait: assert property (handshake_max_wait(awvalid, awready, 1'b1));


  // cov_awvalid_before_awready: cover property (valid_before_ready(awvalid, awready));
  // cov_awready_before_awvalid: cover property (ready_before_valid(awvalid, awready));
  // cov_awready_with_awvalid: cover property (valid_with_ready(awvalid, awready));

  //SECTION W channel prop

	// IMPORTANT will be removed until the main master logic is implemented
  ast_axi_w_stable_wdata: assert property (ast_axi_stable_before_handshake(wvalid, wready, wdata));
  ast_axi_w_stable_wstrb: assert property (ast_axi_stable_before_handshake(wvalid, wready, wstrb));

  ast_axi_w_data_wlast: assert property (ast_axi_data_last(handshake_cnt_w, awlen, wlast));
  ast_axi_w_data_single_burst_wlast: assert property (ast_axi_single_burst_data_last(awlen, wlast, awready, awvalid));
  ast_axi_w_data_single_burst_wlast_stability: assert property (ast_axi_single_burst_data_last_stable(wlast, wready, wvalid));

  // cov_w_data_wlast_axi_c: cover property (wlast);

	//IMPORTANT fails beacuse wvalid does not falls after wlast_axi
  ast_axi_w_wvalid_until_wready: assert property (ast_axi_valid_before_handshake(wvalid, wready));

  //SECTION B channel prop
	ast_axi_b_no_slave_error: assert property(ast_axi_resp(bresp, bvalid));
	

  //SECTION AR channel prop

  ast_axi_ar_stable_araddr: assert property (ast_axi_stable_before_handshake(arvalid, arready, araddr));
  ast_axi_ar_stable_arlen: assert property (ast_axi_stable_before_handshake(arvalid, arready, arlen));
  ast_axi_ar_stable_arsize: assert property (ast_axi_stable_before_handshake(arvalid, arready, arsize));
  ast_axi_ar_stable_arburst: assert property (ast_axi_stable_before_handshake(arvalid, arready, arburst));

  ast_axi_ar_arvalid_until_arready: assert property (ast_axi_valid_before_handshake(arvalid, arready));
	ast_axi_ar_valid_arsize: assert property(ast_axi_size(arvalid, arsize));
  //ast_axi_arready_max_wait: assert property (handshake_max_wait(arvalid, arready, 1'b1));

  // cov_arvalid_c: cover property (arvalid);

  // cov_arvalid_before_arready: cover property (valid_before_ready(arvalid, arready));
  // cov_arready_before_arvalid: cover property (ready_before_valid(arvalid, arready));
  // cov_arready_with_arvalid: cover property (valid_with_ready(arvalid, arready));


  //SECTION R channel prop
	// cov_rdata_val1: cover property(rdata == 32'hBEEFBABA && araddr == 32'h13);
	// cov_rdata_val2: cover property(rdata == 32'hBEEFBABA && araddr == 32'hf);
	// cov_rdata_val3: cover property(araddr == 32'hf ##1 rdata == 32'hBEEFBABA);

	// cov_radddr_val: cover property(araddr == 32'h7);
  // ast_axi_r_stable_rdata: assert property (ast_axi_stable_before_handshake(rvalid, rready, rdata));
  ast_axi_r_data_rlast: assert property (ast_axi_data_last(handshake_cnt_r, arlen, rlast));
  ast_axi_r_data_single_burst_rlast: assert property (ast_axi_single_burst_data_last(arlen, rlast, arready, arvalid));
  ast_axi_r_data_single_burst_rlast_stability: assert property (ast_axi_single_burst_data_last_stable(rlast, rready, rvalid));

	// FIXME Cannot be proved because rready is always true
  // ast_axi_r_rvalid_until_rready: assert property (ast_axi_valid_before_handshake(rvalid, rready));

	ast_axi_r_no_slave_error: assert property(ast_axi_resp(rresp, rvalid));

  // cov_r_rvalid: cover property (rvalid);
  // cov_r_rready: cover property (rready);

  // rvalid_not_rready: cover property (rvalid && !rready);





endchecker


