
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

	reg [7 : 0] handshake_cnt;
  int max_wait = 4;

	//SECTION Aux code

	always @(posedge clk or posedge reset) begin
		if(reset) begin
			handshake_cnt <= 1'b0;
		end
		else begin
			if((wvalid && wready) || (rvalid && rready)) begin
				handshake_cnt <= handshake_cnt + 1'b1;
			end
			else if(wlast || rlast) begin
				handshake_cnt <= 1'b0;
			end
		end
	end

  // SECTION Property definitions

  //NOTE Assert
  property stable_before_handshake(valid, ready, control);
    valid && !ready |=> $stable(control);
  endproperty

  property exit_from_reset(areset, valid);
    ##1 (areset || $rose(areset)) |-> !valid;
  endproperty

  property valid_before_handshake(valid, ready);
    valid && !ready |=> valid;
  endproperty

  property handshake_max_wait(valid, ready, timeout);
    valid && !ready |-> ##[1:timeout] ready;
  endproperty

  property last_data(xlast, axlen);
  (axlen-1) == handshake_cnt |=> xlast;
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

  aw_stable_awaddr: assert property (stable_before_handshake(awvalid, awready, awaddr));
  aw_stable_awlen: assert property (stable_before_handshake(awvalid, awready, awlen));
  aw_stable_awsize: assert property (stable_before_handshake(awvalid, awready, awsize));
  aw_stable_awburst: assert property (stable_before_handshake(awvalid, awready, awburst));

  // aw_exit_reset: assert property (exit_from_reset(reset, awvalid));
  aw_awvalid_until_awready: assert property (valid_before_handshake(awvalid, awready));

  // awready_max_wait: assert property handshake_max_wait(awvalid, awready, max_wait);


  awvalid_before_awready: cover property (valid_before_ready(awvalid, awready));
  // awready_before_awvalid: cover property (ready_before_valid(awvalid, awready));
  awready_with_awvalid: cover property (valid_with_ready(awvalid, awready));

	// BUG unable to cover reset
	// reset_cover: cover property($rose(reset) ##5 $rose(reset));
  

  //SECTION W channel prop

	// IMPORTANT will be removed until the main master logic is implemented
  // w_stable_wdata: assert property (stable_before_handshake(wvalid, wready, wdata));
  w_stable_wstrb: assert property (stable_before_handshake(wvalid, wready, wstrb));
  w_data_wlast: assert property (last_data(wlast, awlen));
  w_data_wlast_c: cover property (wlast);

  // w_exit_reset: assert property (exit_from_reset(reset, wvalid));
  w_wvalid_until_wready: assert property (valid_before_handshake(wvalid, wready));

  //SECTION B channel prop

  //SECTION AR channel prop

  ar_stable_araddr: assert property (stable_before_handshake(arvalid, arready, araddr));
  ar_stable_arlen: assert property (stable_before_handshake(arvalid, arready, arlen));
  ar_stable_arsize: assert property (stable_before_handshake(arvalid, arready, arsize));
  ar_stable_arburst: assert property (stable_before_handshake(arvalid, arready, arburst));

  // ar_exit_reset: assert property (exit_from_reset(reset, arvalid));
  ar_arvalid_until_arready: assert property (valid_before_handshake(arvalid, arready));

  // arready_max_wait: assert property handshake_max_wait(arvalid, arready, max_wait);

  arvalid_c: cover property (arvalid);

  arvalid_before_arready: cover property (valid_before_ready(arvalid, arready));
  // arready_before_arvalid: cover property (ready_before_valid(arvalid, arready));
  arready_with_arvalid: cover property (valid_with_ready(arvalid, arready));


  //SECTION R channel prop

  r_stable_rdata: assert property (stable_before_handshake(rvalid, rready, rdata));
  //r_stable_rstrb: assert property (stable_before_handshake(rvalid, rready, rstrb));
	// IMPORTANT It can not be checked here because
  r_data_rlast: assert property (last_data(rlast, arlen-1));

  // r_exit_reset: assert property (exit_from_reset(reset, rvalid));
  r_rvalid_until_rready: assert property (valid_before_handshake(rvalid, rready));

  r_rvalid: cover property (rvalid);
  r_rready: cover property (rready);





endchecker



