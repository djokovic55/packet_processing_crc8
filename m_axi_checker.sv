checker  m_axi_checker(
	clk	,
	reset	,

	////////////////////////////////////////////////////////////////////////////////
	// MASTER
	////////////////////////////////////////////////////////////////////////////////
	s_axi_int_awaddr,
	s_axi_int_awlen,
	s_axi_int_awsize,
	s_axi_int_awburst,

	s_axi_int_awvalid,
	s_axi_int_awready,

	// WRITE DATA CHANNEL
	s_axi_int_wdata,
	s_axi_int_wstrb,
	s_axi_int_wlast,

	s_axi_int_wvalid,
	s_axi_int_wready,

	// WRITE RESPONSE CHANNEL
	s_axi_int_bresp,

	s_axi_int_bvalid,
	s_axi_int_bready,

	// READ ADDRESS CHANNEL
	s_axi_int_araddr,
	s_axi_int_arlen,
	s_axi_int_arsize,
	s_axi_int_arburst,

	s_axi_int_arvalid,
	s_axi_int_arready,

	// READ DATA CHANNEL
	s_axi_int_rdata,
	s_axi_int_rresp,
	s_axi_int_rlast,

	s_axi_int_rvalid,
	s_axi_int_rready,
	////////////////////////////////////////////////////////////////////////////////

);

	default 
	clocking @(posedge clk);
	endclocking

	default disable iff reset;

	reg aw_hs;
	reg w_hs;
	reg [7:0] w_hs_cnt;
	logic wlast_aux;

	//SECTION Aux code
	// Count the number of valid ready pairs, which represent the number of successful transaction
	// Based on that info generate last signal

	always @(posedge clk or posedge reset) begin
		if(reset) begin
			aw_hs <= 1'b0;
		end
		else begin
			if(s_axi_int_awvalid&& s_axi_int_awready) begin
				aw_hs <= 1'b1;
			end
			// FIX only when the current transaction is over
			else if(s_axi_int_bvalid&& s_axi_int_bready) begin
				aw_hs <= 1'b0;
			end
		end
	end

	always @(posedge clk or posedge reset) begin
		if(reset) begin
			w_hs<= 1'b0;
		end
		else begin
			if(s_axi_int_wvalid&& s_axi_int_wready) begin
				w_hs<= 1'b1;
			end
			else if(s_axi_int_bvalid&& s_axi_int_bready) begin
				w_hs<= 1'b0;
			end
		end
	end

	always @(posedge clk or posedge reset) begin
		if(reset) begin
			w_hs_cnt<= 1'b0;
		end
		else begin
			if(s_axi_int_wvalid&& s_axi_int_wready) begin
				w_hs_cnt<= w_hs_cnt + 1'b1;
			end
			else if(s_axi_int_bvalid && s_axi_int_bready) begin
				w_hs_cnt<= 1'b0;
			end
		end
	end

	assign wlast_aux = w_hs_cnt == s_axi_int_awlen ? 1'b1 : 1'b0;


	//SECTION Master side properties
	//####################################### Stability ######################################### 
	// Write address channel
	awvalid_hold: assume property (s_axi_int_awvalid && !s_axi_int_awready |=> s_axi_int_awvalid );
	awvalid_drop: assume property (aw_hs |=> !s_axi_int_awvalid );

	awaddr_hold: assume property ( (s_axi_int_awvalid && !s_axi_int_awready ) |=> $stable(s_axi_int_awaddr ) );
	awaddr_value1: assume property ( s_axi_int_awaddr [31:16] == 16'h0000);

	// awlen_hold: assume property ( (s_axi_int_awvalid && !s_axi_int_awready ) |=> $stable(s_axi_int_awlen ) );
	awlen_value: assume property( s_axi_int_awlen == 8'd3);

	awsize_hold: assume property ( (s_axi_int_awvalid && !s_axi_int_awready ) |=> $stable(s_axi_int_awsize ) );
	awburst_hold: assume property ( (s_axi_int_awvalid && !s_axi_int_awready ) |=> $stable(s_axi_int_awburst ) );

	// Write channel signals get value only after successful handshake on write address channel  

	wvalid_hold: assume property (s_axi_int_wvalid && !s_axi_int_wready |=> s_axi_int_wvalid );
	wstrb_hold: assume property(!w_hs |-> $stable(s_axi_int_wstrb ));
	wlast_gen: assume property(s_axi_int_wlast == wlast_aux);

	// Write response channel
	bready_hold: assume property(s_axi_int_wlast |=> s_axi_int_bready ); 

	// Assume that read is not possible 
	arvalid_shut: assume property(!s_axi_int_arvalid );
	rvalid_shut: assume property(!s_axi_int_rvalid );


	//SECTION Slave side properties
	awready_gen_inmem : assume property (m_axi_int_awvalid_inmem && !m_axi_int_awready_inmem |=> m_axi_int_awready_inmem); 

	wready_gen_inmem : assume property (m_axi_int_wvalid_inmem && !m_axi_int_wready_inmem |=> m_axi_int_wready_inmem); 

	bvalid_gen_inmem : assume property (m_axi_int_wlast_inmem |=> m_axi_int_bvalid_inmem); 

	//SECTION Other properties
	// assume that gnt is always 0001 -> only gn - inmem communication
	
	//SECTION COVER

	//BUG illegal property
	awvalid_gn_c1: cover property(s_axi_int_awvalid [*5]);

	awvalid_inmem_c: cover property(m_axi_int_awvalid_inmem[*5]);
	gn_inmem_com_c: cover property(m_axi_int_awvalid_inmem ##5 s_axi_int_awready );
	gn_handshake_c: cover property(s_axi_int_awvalid ##5 s_axi_int_awready );
	awvalid_gn_to_inmem: cover property(s_axi_int_awvalid ##[0:2] m_axi_int_awvalid_inmem);
	
	wlast: cover property(w_hs_cnt_gn == 3 &&  m_axi_int_wlast_inmem ##[1:$] m_axi_int_bvalid_inmem && m_axi_int_bready_inmem);

	handshake_cnt: cover property(w_hs_cnt_gn == 3);


endchecker



