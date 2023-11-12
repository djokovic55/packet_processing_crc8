
module checker_pb(
  input logic clk,
  input logic reset,

  input logic start_i,
  output logic busy_o,
  output logic irq_o,
  input logic[31:0] addr_hdr_i,
  input logic ignore_ecc_err_i,
  output logic pkt_ecc_corr_o,
  output logic pkt_ecc_uncorr_o,
  output logic pkt_crc_err_o,
  output logic[3:0] pkt_byte_cnt_o,
  output logic[3:0] pkt_type_o,

  input logic[31:0] s_axi_awaddr,
  input logic[7:0] s_axi_awlen,
  input logic[2:0] s_axi_awsize,
  input logic[1:0] s_axi_awburst,
  input logic s_axi_awvalid,
  output logic s_axi_awready, //TODO

  input logic[31:0] s_axi_wdata,
  input logic[3:0] s_axi_wstrb,
  input logic s_axi_wlast,
  input logic s_axi_wvalid,
  output logic s_axi_wready, //TODO

  output logic[1:0] s_axi_bresp, //TODO
  output logic s_axi_bvalid, //TODO
  input logic s_axi_bready,
  
  input logic[31:0] s_axi_araddr,
  input logic[7:0] s_axi_arlen,
  input logic[2:0] s_axi_arsize,
  input logic[1:0] s_axi_arburst,
  input logic s_axi_arvalid,
  output logic s_axi_arready, //TODO

  output logic[31:0] s_axi_rdata,//TODO
  output logic[1:0] s_axi_rresp,//TODO
  output logic s_axi_rlast,//TODO
  output logic s_axi_rvalid,//TODO
  input logic s_axi_rready

);

	default clocking @(posedge clk);
	endclocking

	default disable iff reset;

  property aux_eq(sig, sig_aux);
    sig == sig_aux;
  endproperty

  reg[7:0] awlen, awlen_cntr;
  reg[7:0] arlen, arlen_cntr;
  logic awready, wready;
  reg bvalid;
  reg arready;
  logic[31:0] rdata;
  reg rlast, rvalid;
  reg[1:0] bresp, rresp;

  reg axi_awv_awr_flag, axi_arv_arr_flag;

  asm_addr_hdr_i: assume property (addr_hdr_i == 32'hBABABABA);
  asm_ignore_ecc_err: assume property (ignore_ecc_err_i == 1'b1);

  //SECTION Check and cover
  cov_pp_start: cover property(start_i == 1'b1);

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
			else if (s_axi_awlen == '0 && wready == 1'b1) 
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
			else if(s_axi_wlast == 1'b1 && wready == 1'b1) 
				wready <= 1'b0;
			//single burst
			else if(s_axi_awlen == '0 && wready == 1'b1) begin 
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
			if (axi_awv_awr_flag == 1'b1 && wready == 1'b1 && s_axi_wvalid == 1'b1 && bvalid == 1'b0 && (s_axi_wlast == 1'b1 || s_axi_awlen == '0)) begin
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
			else if(((arlen_cntr == arlen - 1'b1)) && rnext == 1'b1 && axi_arv_arr_flag == 1'b1)
				rlast <= 1'b1;
			else if (rlast == 1'b1 || arlen == '0) 
				rlast <= 1'b0;
		end 
	end

	// Burst length counter
	always @(posedge clk) begin
		if(reset) begin
			arlen_cntr <= 8'h0;
		end
		else begin
			//FIX missing reset condition
			if(!arready && s_axi_arvalid && !axi_arv_arr_flag)
				arlen_cntr <= 8'h0;
			else if((arlen_cntr < arlen) && rnext) 
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
endmodule