checker  checker_int(
	clk	,
	reset	,

	////////////////////////////////////////////////////////////////////////////////
	// MASTERS
	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF CONTROLLER MODULE M1
	////////////////////////////////////////////////////////////////////////////////
	s_axi_int_awaddr_ctrl,
	s_axi_int_awlen_ctrl,
	s_axi_int_awsize_ctrl,
	s_axi_int_awburst_ctrl,

	s_axi_int_awvalid_ctrl,
	s_axi_int_awready_ctrl,

	// WRITE DATA CHANNEL
	s_axi_int_wdata_ctrl,
	s_axi_int_wstrb_ctrl,
	s_axi_int_wlast_ctrl,

	s_axi_int_wvalid_ctrl,
	s_axi_int_wready_ctrl,

	// WRITE RESPONSE CHANNEL
	s_axi_int_bresp_ctrl,

	s_axi_int_bvalid_ctrl,
	s_axi_int_bready_ctrl,

	// READ ADDRESS CHANNEL
	s_axi_int_araddr_ctrl,
	s_axi_int_arlen_ctrl,
	s_axi_int_arsize_ctrl,
	s_axi_int_arburst_ctrl,

	s_axi_int_arvalid_ctrl,
	s_axi_int_arready_ctrl,

	// READ DATA CHANNEL
	s_axi_int_rdata_ctrl,
	s_axi_int_rresp_ctrl,
	s_axi_int_rlast_ctrl,

	s_axi_int_rvalid_ctrl,
	s_axi_int_rready_ctrl,
	////////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF PACKET BUILDING 0 MODULE M2
	////////////////////////////////////////////////////////////////////////////////

	// WRITE ADDRESS CHANNEL
	s_axi_int_awaddr_pb0,
	s_axi_int_awlen_pb0,
	s_axi_int_awsize_pb0,
	s_axi_int_awburst_pb0,

	s_axi_int_awvalid_pb0,
	s_axi_int_awready_pb0,

	// WRITE DATA CHANNEL
	s_axi_int_wdata_pb0,
	s_axi_int_wstrb_pb0,
	s_axi_int_wlast_pb0,

	s_axi_int_wvalid_pb0,
	s_axi_int_wready_pb0,

	// WRITE RESPONSE CHANNEL
	s_axi_int_bresp_pb0,

	s_axi_int_bvalid_pb0,
	s_axi_int_bready_pb0,

	// READ ADDRESS CHANNEL
	s_axi_int_araddr_pb0,
	s_axi_int_arlen_pb0,
	s_axi_int_arsize_pb0,
	s_axi_int_arburst_pb0,

	s_axi_int_arvalid_pb0,
	s_axi_int_arready_pb0,

	// READ DATA CHANNEL
	s_axi_int_rdata_pb0,
	s_axi_int_rresp_pb0,
	s_axi_int_rlast_pb0,

	s_axi_int_rvalid_pb0,
	s_axi_int_rready_pb0,
	////////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF PACKET BUILDING 1 MODULE M3
	////////////////////////////////////////////////////////////////////////////////
	
	// WRITE ADDRESS CHANNEL
	s_axi_int_awaddr_pb1,
	s_axi_int_awlen_pb1,
	s_axi_int_awsize_pb1,
	s_axi_int_awburst_pb1,
	s_axi_int_awvalid_pb1,
	s_axi_int_awready_pb1,

	// WRITE DATA CHANNEL
	s_axi_int_wdata_pb1,
	s_axi_int_wstrb_pb1,
	s_axi_int_wlast_pb1,
	s_axi_int_wvalid_pb1,
	s_axi_int_wready_pb1,

	// WRITE RESPONSE CHANNEL
	s_axi_int_bresp_pb1,
	s_axi_int_bvalid_pb1,
	s_axi_int_bready_pb1,

	// READ ADDRESS CHANNEL
	s_axi_int_araddr_pb1,
	s_axi_int_arlen_pb1,
	s_axi_int_arsize_pb1,
	s_axi_int_arburst_pb1,
	s_axi_int_arvalid_pb1,
	s_axi_int_arready_pb1,

	// READ DATA CHANNEL
	s_axi_int_rdata_pb1,
	s_axi_int_rresp_pb1,
	s_axi_int_rlast_pb1,
	s_axi_int_rvalid_pb1,
	s_axi_int_rready_pb1,
	////////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF PACKET PARSING MODULE M4
	////////////////////////////////////////////////////////////////////////////////
	
	// WRITE ADDRESS CHANNEL
	s_axi_int_awaddr_pp,
	s_axi_int_awlen_pp,
	s_axi_int_awsize_pp,
	s_axi_int_awburst_pp,
	s_axi_int_awvalid_pp,
	s_axi_int_awready_pp,

	// WRITE DATA CHANNEL
	s_axi_int_wdata_pp,
	s_axi_int_wstrb_pp,
	s_axi_int_wlast_pp,
	s_axi_int_wvalid_pp,
	s_axi_int_wready_pp,

	// WRITE RESPONSE CHANNEL
	s_axi_int_bresp_pp,
	s_axi_int_bvalid_pp,
	s_axi_int_bready_pp,

	// READ ADDRESS CHANNEL
	s_axi_int_araddr_pp,
	s_axi_int_arlen_pp,
	s_axi_int_arsize_pp,
	s_axi_int_arburst_pp,
	s_axi_int_arvalid_pp,
	s_axi_int_arready_pp,

	// READ DATA CHANNEL
	s_axi_int_rdata_pp,
	s_axi_int_rresp_pp,
	s_axi_int_rlast_pp,
	s_axi_int_rvalid_pp,
	s_axi_int_rready_pp,
	////////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////////
	// SLAVES
	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF INCOMING MEMORY MODULE S1
	////////////////////////////////////////////////////////////////////////////////

	// ADDRESS WRITE CHANNEL
	m_axi_int_awaddr_inmem,
	m_axi_int_awlen_inmem,
	m_axi_int_awsize_inmem,
	m_axi_int_awburst_inmem,
	m_axi_int_awvalid_inmem,
	m_axi_int_awready_inmem,

	// WRITE DATA CHANNEL
	m_axi_int_wdata_inmem,
	m_axi_int_wstrb_inmem,
	m_axi_int_wlast_inmem,
	m_axi_int_wvalid_inmem,
	m_axi_int_wready_inmem,

	// WRITE RESPONSE CHANNEL
	m_axi_int_bresp_inmem,
	m_axi_int_bvalid_inmem,
	m_axi_int_bready_inmem,

	// READ ADDRESS CHANNEL
	m_axi_int_araddr_inmem,
	m_axi_int_arlen_inmem,
	m_axi_int_arsize_inmem,
	m_axi_int_arburst_inmem,
	m_axi_int_arvalid_inmem,
	m_axi_int_arready_inmem,

	// READ DATA CHANNEL
	m_axi_int_rdata_inmem,
	m_axi_int_rresp_inmem,
	m_axi_int_rlast_inmem,
	m_axi_int_rvalid_inmem,
	m_axi_int_rready_inmem,
	////////////////////////////////////////////////////////////////////////////////

	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF OUTGOING MEMORY MODULE S2
	////////////////////////////////////////////////////////////////////////////////

	// ADDRESS WRITE CHANNEL
	m_axi_int_awaddr_outmem,
	m_axi_int_awlen_outmem,
	m_axi_int_awsize_outmem,
	m_axi_int_awburst_outmem,
	m_axi_int_awvalid_outmem,
	m_axi_int_awready_outmem,

	// WRITE DATA CHANNEL
	m_axi_int_wdata_outmem,
	m_axi_int_wstrb_outmem,
	m_axi_int_wlast_outmem,
	m_axi_int_wvalid_outmem,
	m_axi_int_wready_outmem,

	// WRITE RESPONSE CHANNEL
	m_axi_int_bresp_outmem,
	m_axi_int_bvalid_outmem,
	m_axi_int_bready_outmem,

	// READ ADDRESS CHANNEL
	m_axi_int_araddr_outmem,
	m_axi_int_arlen_outmem,
	m_axi_int_arsize_outmem,
	m_axi_int_arburst_outmem,
	m_axi_int_arvalid_outmem,
	m_axi_int_arready_outmem,

	// READ DATA CHANNEL
	m_axi_int_rdata_outmem,
	m_axi_int_rresp_outmem,
	m_axi_int_rlast_outmem,
	m_axi_int_rvalid_outmem,
	m_axi_int_rready_outmem,
	////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF REGISTERS MODULE S3
	////////////////////////////////////////////////////////////////////////////////

	// ADDRESS WRITE CHANNEL
	m_axi_int_awaddr_reg,
	m_axi_int_awlen_reg,
	m_axi_int_awsize_reg,
	m_axi_int_awburst_reg,
	m_axi_int_awvalid_reg,
	m_axi_int_awready_reg,

	// WRITE DATA CHANNEL
	m_axi_int_wdata_reg,
	m_axi_int_wstrb_reg,
	m_axi_int_wlast_reg,
	m_axi_int_wvalid_reg,
	m_axi_int_wready_reg,

	// WRITE RESPONSE CHANNEL
	m_axi_int_bresp_reg,
	m_axi_int_bvalid_reg,
	m_axi_int_bready_reg,

	// READ ADDRESS CHANNEL
	m_axi_int_araddr_reg,
	m_axi_int_arlen_reg,
	m_axi_int_arsize_reg,
	m_axi_int_arburst_reg,
	m_axi_int_arvalid_reg,
	m_axi_int_arready_reg,

	// READ DATA CHANNEL
	m_axi_int_rdata_reg,
	m_axi_int_rresp_reg,
	m_axi_int_rlast_reg,
	m_axi_int_rvalid_reg,
	m_axi_int_rready_reg,
	////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////////
	// INTCON PORTS OF EXTERNAL REGISTERS MODULE S4
	////////////////////////////////////////////////////////////////////////////////

	// ADDRESS WRITE CHANNEL
	m_axi_int_awaddr_exreg,
	m_axi_int_awlen_exreg,
	m_axi_int_awsize_exreg,
	m_axi_int_awburst_exreg,
	m_axi_int_awvalid_exreg,
	m_axi_int_awready_exreg,

	// WRITE DATA CHANNEL
	m_axi_int_wdata_exreg,
	m_axi_int_wstrb_exreg,
	m_axi_int_wlast_exreg,
	m_axi_int_wvalid_exreg,
	m_axi_int_wready_exreg,

	// WRITE RESPONSE CHANNEL
	m_axi_int_bresp_exreg,
	m_axi_int_bvalid_exreg,
	m_axi_int_bready_exreg,

	// READ ADDRESS CHANNEL
	m_axi_int_araddr_exreg,
	m_axi_int_arlen_exreg,
	m_axi_int_arsize_exreg,
	m_axi_int_arburst_exreg,
	m_axi_int_arvalid_exreg,
	m_axi_int_arready_exreg,

	// READ DATA CHANNEL
	m_axi_int_rdata_exreg,
	m_axi_int_rresp_exreg,
	m_axi_int_rlast_exreg,
	m_axi_int_rvalid_exreg,
	m_axi_int_rready_exreg
	////////////////////////////////////////////////////////////////////////////////
);

	default 
	clocking @(posedge clk);
	endclocking

	default disable iff reset;

	reg aw_hs_ctrl;
	reg w_hs_ctrl;

	//SECTION Aux code
	// Count the number of valid ready pairs, which represent the number of successful transaction
	// Based on that info generate last signal
	always @(posedge clk or posedge reset) begin
		if(reset) begin
			aw_hs_ctrl <= 1'b0;
		end
		else begin
			if(s_axi_int_awvalid_ctrl && s_axi_int_awready_ctrl) begin
				aw_hs_ctrl <= 1'b1;
			end
			// FIX only when the current transaction is over
			else if(s_axi_int_bvalid_ctrl && s_axi_int_bready_ctrl) begin
				aw_hs_ctrl <= 1'b0;
			end
		end
	end

	always @(posedge clk or posedge reset) begin
		if(reset) begin
			w_hs_ctrl <= 1'b0;
		end
		else begin
			if(s_axi_int_wvalid_ctrl && s_axi_int_wready_ctrl) begin
				w_hs_ctrl <= 1'b1;
			end
			else if(s_axi_int_bvalid_ctrl && s_axi_int_bready_ctrl) begin
				w_hs_ctrl <= 1'b0;
			end
		end
	end


	//SECTION Master side properties
	//####################################### Stability ######################################### 
	// Write address channel
	awvalid_hold_ctrl : assume property (s_axi_int_awvalid_ctrl  && !s_axi_int_awready_ctrl |=> s_axi_int_awvalid_ctrl);
	awvalid_drop_ctrl : assume property (aw_hs_ctrl |=> !s_axi_int_awvalid_ctrl);

	awaddr_hold_ctrl : assume property ( (s_axi_int_awvalid_ctrl && !s_axi_int_awready_ctrl) |=> $stable(s_axi_int_awaddr_ctrl) );
	awaddr_value_ctrl : assume property ( s_axi_int_awaddr_ctrl[23:16] == 8'h00);

	awlen_hold_ctrl : assume property ( (s_axi_int_awvalid_ctrl && !s_axi_int_awready_ctrl) |=> $stable(s_axi_int_awlen_ctrl) );
	awsize_hold_ctrl : assume property ( (s_axi_int_awvalid_ctrl && !s_axi_int_awready_ctrl) |=> $stable(s_axi_int_awsize_ctrl) );
	awburst_hold_ctrl : assume property ( (s_axi_int_awvalid_ctrl && !s_axi_int_awready_ctrl) |=> $stable(s_axi_int_awburst_ctrl) );

	// Write channel signals get value only after successful handshake on write address channel  
	wvalid_write_phase_hold_ctrl: assume property(!aw_hs_ctrl |-> !s_axi_int_wvalid_ctrl);
	wvalid_hold_ctrl : assume property (s_axi_int_wvalid_ctrl  && !s_axi_int_wready_ctrl |=> s_axi_int_wvalid_ctrl);

	wstrb_hold_ctrl: assume property(!w_hs_ctrl |-> $stable(s_axi_int_wstrb_ctrl));
	wlast_hold_ctrl: assume property(!w_hs_ctrl |-> !s_axi_int_wlast_ctrl);

	// wvalid_gen_ctrl: assume property(aw_hs_ctrl |=> s_axi_int_wvalid_ctrl);

	// Write response channel
	bready_hold_ctrl: assume property(w_hs_ctrl |=> s_axi_int_bready_ctrl); 

	// Assume that read is not possible 
	arvalid_shut_ctrl: assume property(!s_axi_int_arvalid_ctrl)
	rvalid_shut_ctrl: assume property(!s_axi_int_rvalid_ctrl)


	//SECTION Slave side properties
	awready_gen_inmem : assume property (m_axi_int_awvalid_inmem |=> m_axi_int_awready_inmem); 
	wready_gen_inmem : assume property (m_axi_int_wvalid_inmem |=> m_axi_int_wready_inmem); 
	// bvalid_gen_inmem : assume property (m_axi_int_wvalid_inmem |=> m_axi_int_wready_inmem); 

	//SECTION Other properties
	// assume that gnt is always 0001 -> only ctrl - inmem communication
	
	//OPTIMIZE COVER

	awready_ctrl_c: cover property(!s_axi_int_awready_ctrl ##1 !s_axi_int_awready_ctrl);
	awvalid_inmem_c: cover property(m_axi_int_awvalid_inmem);
	ctrl_inmem_com: cover property(m_axi_int_awvalid_inmem && s_axi_int_awready_ctrl);

endchecker



