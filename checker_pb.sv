checker checker_pb(
  clk,
  reset,

  start_i,
  busy_o,
  irq_o,
  addr_in_i,
  byte_cnt_i,
  pkt_type_i,
  ecc_en_i,
  crc_en_i,
  ins_ecc_err_i,
  ins_crc_err_i,
  ecc_val_i,
  crc_val_i,
  sop_val_i,
  data_sel_i,
  addr_out_i,

  s_axi_awaddr,
  s_axi_awlen,
  s_axi_awsize,
  s_axi_awburst,
  s_axi_awvalid,
  s_axi_awready, //TODO

  s_axi_wdata,
  s_axi_wstrb,
  s_axi_wlast,
  s_axi_wvalid,
  s_axi_wready, //TODO

  s_axi_bresp, //TODO
  s_axi_bvalid, //TODO
  s_axi_bready,
  
  s_axi_araddr,
  s_axi_arlen,
  s_axi_arsize,
  s_axi_arburst,
  s_axi_arvalid,
  s_axi_arready, //TODO

  s_axi_rdata,//TODO
  s_axi_rresp,//TODO
  s_axi_rlast,//TODO
  s_axi_rvalid,//TODO
  s_axi_rready

);

	default clocking @(posedge clk);
	endclocking

	default disable iff reset;

  property aux_eq(sig, sig_aux);
    sig == sig_aux;
  endproperty

  reg[7:0] awlen, awlen_cntr;
  reg[7:0] arlen, arlen_cntr;
  reg awready, wready;
  reg bvalid;
  reg arready;
  logic[31:0] rdata;
  reg rlast, rvalid;
  reg[1:0] bresp, rresp;

  reg axi_awv_awr_flag, axi_arv_arr_flag;
  //SECTION Check and cover
  cov_pb_start: cover property(start_i == 1'b1);

  //SECTION Regs config logic
	asm_max_byte_cnt: assume property(byte_cnt_i == 4'h8 );
	asm_stable_max_byte_cnt: assume property($stable(byte_cnt_i));
	asm_merging_option: assume property(data_sel_i == 4'h0);
	asm_merg_op_stability: assume property($stable(data_sel_i));
	asm_crc_en: assume property(crc_en_i == 1'b1);
	asm_ecc_en: assume property(ecc_en_i == 1'b1);
  // asm_start: assume property();
  asm_addr_in: assume property(addr_in_i == 32'hBABABABA);
  asm_pkt_type: assume property(pkt_type_i == 4'hA);
  asm_ins_ecc_err: assume property(ins_ecc_err_i == 1'b0);
  asm_ins_crc_err: assume property(ins_crc_err_i == 1'b0);
  asm_ecc_val: assume property(ecc_val_i == 4'h0);
  asm_crc_val: assume property(crc_val_i == 8'hCC);
  asm_sop_val: assume property(sop_val_i == 3'h7);
  asm_addr_out: assume property(addr_out_i == 32'hBABABABA);


  //SECTION Axi slave response logic

  asm_awready: assume property (aux_eq(s_axi_awready, awready));
  asm_wready: assume property (aux_eq(s_axi_wready, wready));
  asm_bresp: assume property (aux_eq(s_axi_bresp, bresp));
  asm_bvalid: assume property (aux_eq(s_axi_bvalid, bvalid));
  asm_arready: assume property (aux_eq(s_axi_arready, arready));

  asm_rdata: assume property (s_axi_rdata == 32'hDEADBEEF);
  asm_rresp: assume property (aux_eq(s_axi_rresp, rresp));
  asm_rlast: assume property (aux_eq(s_axi_rlast, rlast));
  asm_rvalid: assume property (aux_eq(s_axi_rvalid, rvalid));

  //awready
  always @(posedge clk) begin
		if(reset) begin
			awready <= 1'b0;
			axi_awv_awr_flag <= 1'b0;
		end
		else begin
			if(awready == 1'b0 && s_axi_awvalid == 1'b1 && axi_awv_awr_flag == 1'b0 && axi_arv_arr_flag == 1'b0) begin
				axi_awv_awr_flag  <= 1'b1; 
				awready <= 1'b1;
			end
			else if (s_axi_wlast == 1'b1 && wready == 1'b1) 
				axi_awv_awr_flag  <= 1'b0;
			else
				awready <= 1'b0;
		end
	end

  // aw channel latching
	always @(posedge clk) begin
		if (reset) begin
			awlen <= 8'h0; 
			awlen_cntr <= 8'h0;
		end
		else begin
			if (awready == 1'b0 && s_axi_awvalid == 1'b1 && axi_awv_awr_flag == 1'b0) begin
				awlen_cntr <= 8'h0;
				awlen <= 8'h0;
			end
			else if((awlen_cntr <= awlen) && wready == 1'b1 && s_axi_wvalid == 1'b1)
				awlen_cntr <= awlen_cntr + 1'b1;
		end 
	end
  
  //wready
	always @(posedge clk) begin
		if (reset) begin
			wready <= 1'b0;
		end
		else begin
			if(wready == 1'b0 && s_axi_wvalid == 1'b1 && axi_awv_awr_flag == 1'b1) begin
				wready <= 1'b1;
			end
			else if(s_axi_wlast == 1'b1 && wready == 1'b1) begin 
				wready <= 1'b0;
			end
		end 
	end

  // write response
	always @(posedge clk) begin
		if (reset) begin
			bvalid  <= 1'b0;
			bresp  <= 2'b00; 
		end
		else begin
			if (axi_awv_awr_flag == 1'b1 && wready == 1'b1 && s_axi_wvalid == 1'b1 && bvalid == 1'b0 && s_axi_wlast == 1'b1 ) begin
				bvalid <= 1'b1;
				bresp  <= 2'b00; 
			end
			else if (s_axi_bready == 1'b1 && bvalid == 1'b1) 
				bvalid <= 1'b0;                      
		end
	end         
	//READ CHANNEL
	logic rnext = s_axi_rready && rvalid;

  //arready
	always @(posedge clk) begin
		if (reset) begin
			arready <= 1'b0;
			axi_arv_arr_flag <= 1'b0;
		end
		else begin
			if (arready == 1'b0 && s_axi_arvalid == 1'b1 && axi_awv_awr_flag == 1'b0 && axi_arv_arr_flag == 1'b0) begin
				arready <= 1'b1;
				axi_arv_arr_flag <= 1'b1;
			end
			else if (rvalid == 1'b1 && s_axi_rready == 1'b1 && (arlen_cntr == arlen))  
				axi_arv_arr_flag <= 1'b0;
			else
				arready <= 1'b0;
		end 
	end         

  //ar channel latching
	always @(posedge clk) begin
		if (reset) begin
			arlen <= 8'h0; 
			rlast <= 1'b0;
		end
		else begin
			if (arready == 1'b0 && s_axi_arvalid == 1'b1 && axi_arv_arr_flag == 1'b0) begin
				arlen <= s_axi_arlen;
				rlast <= 1'b0;
			end
			//BUG rnext added
			else if((((arlen_cntr == arlen - 1'b1) && rnext) || (arlen == 8'h0)) && rlast == 1'b0 && axi_arv_arr_flag == 1'b1)
				rlast <= 1'b1;
			else if (rnext) 
				rlast <= 1'b0;
			else if(rlast == 1'b1 && arlen == 8'h0)
				rlast <= 1'b0;
		end 
	end

	// Burst length counter
	always @(posedge clk) begin
		if(reset) begin
			arlen_cntr <= 8'h0;
		end
		else begin
			if((arlen_cntr < arlen) && rnext) 
				arlen_cntr <= arlen_cntr + 1'b1;
		end
	end 

  // rvalid, read response
	always @(posedge clk) begin
		if (reset) begin
			rvalid  <= 1'b0;
			rresp  <= 2'b00; 
		end
		else begin
			if (axi_arv_arr_flag == 1'b1 && s_axi_rvalid == 1'b0) begin
				rvalid <= 1'b1;
				rresp  <= 2'b00; 
			end
			else if (s_axi_rready == 1'b1 && rvalid == 1'b1 && arlen_cntr == arlen) 
				rvalid <= 1'b0;                      
		end
	end         

endchecker
