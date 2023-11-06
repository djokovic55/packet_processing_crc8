
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
			if(wvalid && wready && !wlast) begin
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
			if(rvalid && rready && !rlast) begin
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
  property stable_before_handshake(valid, ready, control);
    valid && !ready |=> $stable(control);
  endproperty

  property valid_before_handshake(valid, ready);
    valid && !ready |=> valid;
  endproperty

  property handshake_max_wait(valid, ready, timeout);
    valid && !ready |-> ##[0:timeout] ready;
  endproperty

  property data_last (xvalid, handshake_cnt, axlen, xlast);
		  xvalid && (handshake_cnt == axlen) && (axlen != '0) |-> xlast;
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

  ast_aw_stable_awaddr: assert property (stable_before_handshake(awvalid, awready, awaddr));
  ast_aw_stable_awlen: assert property (stable_before_handshake(awvalid, awready, awlen));
  ast_aw_stable_awsize: assert property (stable_before_handshake(awvalid, awready, awsize));
  ast_aw_stable_awburst: assert property (stable_before_handshake(awvalid, awready, awburst));
  ast_aw_awvalid_until_awready: assert property (valid_before_handshake(awvalid, awready));
  ast_awready_max_wait: assert property (handshake_max_wait(awvalid, awready, 1'b1));


  // cov_awvalid_before_awready: cover property (valid_before_ready(awvalid, awready));
  // cov_awready_before_awvalid: cover property (ready_before_valid(awvalid, awready));
  // cov_awready_with_awvalid: cover property (valid_with_ready(awvalid, awready));

  //SECTION W channel prop

	// IMPORTANT will be removed until the main master logic is implemented
  ast_w_stable_wdata: assert property (stable_before_handshake(wvalid, wready, wdata));
  ast_w_stable_wstrb: assert property (stable_before_handshake(wvalid, wready, wstrb));
  ast_w_data_wlast: assert property (data_last(wvalid, handshake_cnt_w, awlen, wlast));

  cov_w_data_wlast_c: cover property (wlast);

	//IMPORTANT fails beacuse wvalid does not falls after wlast
  ast_w_wvalid_until_wready: assert property (valid_before_handshake(wvalid, wready));

  //SECTION B channel prop
	ast_b_no_slave_error: assert property(bvalid && bready |-> bresp == 2'b00);
	

  //SECTION AR channel prop

  ast_ar_stable_araddr: assert property (stable_before_handshake(arvalid, arready, araddr));
  ast_ar_stable_arlen: assert property (stable_before_handshake(arvalid, arready, arlen));
  ast_ar_stable_arsize: assert property (stable_before_handshake(arvalid, arready, arsize));
  ast_ar_stable_arburst: assert property (stable_before_handshake(arvalid, arready, arburst));

  ast_ar_arvalid_until_arready: assert property (valid_before_handshake(arvalid, arready));
  ast_arready_max_wait: assert property (handshake_max_wait(arvalid, arready, 1'b1));

  // cov_arvalid_c: cover property (arvalid);

  // cov_arvalid_before_arready: cover property (valid_before_ready(arvalid, arready));
  // cov_arready_before_arvalid: cover property (ready_before_valid(arvalid, arready));
  // cov_arready_with_arvalid: cover property (valid_with_ready(arvalid, arready));


  //SECTION R channel prop

  // ast_r_stable_rdata: assert property (stable_before_handshake(rvalid, rready, rdata));
  ast_r_data_rlast: assert property (data_last(rvalid, handshake_cnt_r, arlen, rlast));

	// FIXME Cannot be proved because rready is always true
  // ast_r_rvalid_until_rready: assert property (valid_before_handshake(rvalid, rready));

	ast_r_no_slave_error: assert property(rvalid && rready |-> rresp == 2'b00);

  // cov_r_rvalid: cover property (rvalid);
  // cov_r_rready: cover property (rready);

  // rvalid_not_rready: cover property (rvalid && !rready);





endchecker


