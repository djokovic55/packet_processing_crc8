
module checker_data_integrity(
  input clk,
  input reset,

  input[3:0] byte_cnt,
  input[3:0] data_sel,

  input[31:0] wdata,
  input wvalid,
  input wlast,
  input wready, 

  input[31:0] rdata,
  input rlast,
  input rvalid,
  input rready

);

	default clocking @(posedge clk);
	endclocking

	default disable iff reset;

  reg[4:0] wpulse_cnt; 
  reg[3:0] rpulse_cnt;

  // handshake flags
  logic wnext = wvalid && wready;
  logic rnext = rvalid && rready;

  // write and read channel handshake counter
  always @(posedge clk) begin
    if(reset) begin
      wpulse_cnt <= '0; 
      rpulse_cnt <= '0; 
    end
    else begin
      if(wnext && !wlast)
        wpulse_cnt <= wpulse_cnt + 1;
      else if(wnext && wlast)
        wpulse_cnt <= '0; 

      if(rnext && !rlast)
        rpulse_cnt <= rpulse_cnt + 1;
      else if(rnext && rlast)
        rpulse_cnt <= '0; 
    end
  end

  //////////////////////////////////////////////////////////////////////////////// 
  // Packet IN interface
  //////////////////////////////////////////////////////////////////////////////// 

  logic[3:0] chosen_byte;

  asm_chosen_byte_stable: assume property($stable(chosen_byte));

  asm_chosen_byte_op0: assume property(disable iff(reset)
    data_sel == 4'h0 |-> chosen_byte <= byte_cnt && chosen_byte[1:0] == 2'b0);

  asm_chosen_byte_op1: assume property(disable iff(reset)
    data_sel == 4'h1 |-> chosen_byte <= byte_cnt && chosen_byte[1] == 1'b0);
  
  asm_chosen_byte_op2: assume property(disable iff(reset)
    data_sel == 4'h2 |-> chosen_byte <= byte_cnt);

  reg[7:0] chosen_byte_data;
  logic chosen_byte_flag;
  const logic[3:0] OP0 = 4'h0;
  const logic[3:0] OP1 = 4'h1;
  const logic[3:0] OP2 = 4'h2;

  // store chosen byte data
  always @(posedge clk) begin
    if(reset) begin
      chosen_byte_data <= '0; 
	  chosen_byte_flag <= 1'b0;	
    end
    else begin
	  if(chosen_byte[3:2] == rpulse_cnt && rnext) begin
		chosen_byte_flag <= 1'b1;
		if(chosen_byte_flag)
		  chosen_byte_flag <= 1'b0;	

		case(data_sel) 
		  OP0: begin
			chosen_byte_data <= rdata[7:0];
		  end
		  OP1: begin
			case(chosen_byte[0]) 
			  1'b0: chosen_byte_data <= rdata[7:0];
			  1'b1: chosen_byte_data <= rdata[15:8];
			endcase
		  end
		  OP2: begin
			case(chosen_byte[1:0]) 
			  2'b00: chosen_byte_data <= rdata[7:0];
			  2'b01: chosen_byte_data <= rdata[15:8];
			  2'b10: chosen_byte_data <= rdata[23:16];
			  2'b11: chosen_byte_data <= rdata[31:24];
			endcase
		  end
		endcase
	  end
    end
  end

 //////////////////////////////////////////////////////////////////////////////// 
 // Packet OUT interface
 //////////////////////////////////////////////////////////////////////////////// 

  logic[4:0] received_byte; 
  always @(posedge clk) begin
    if(reset) begin
      received_byte <= '0;
    end
    else begin
      case(data_sel) 
        OP0: received_byte <= (chosen_byte[3:2] + 2);
        OP1: received_byte <= ((chosen_byte[3:2] * 2) + chosen_byte[0] + 2);
        default: received_byte <= (chosen_byte + 2); 
      endcase
    end
  end

  // Indication that chosen packet arrived at the output
  logic chosen_packet_arrived;
  reg[7:0] received_byte_data;


  // store received data byte
  always @(posedge clk) begin
    if(reset) begin
      received_byte_data <= '0; 
      chosen_packet_arrived <= 1'b0;
    end
    else begin
	  //default
	  chosen_packet_arrived <= 1'b0; //generate pulse

	  // extract byte only when in OUTMEM_WRITE phase
      if(received_byte[4:2] == wpulse_cnt && wnext) begin

        chosen_packet_arrived <= 1'b1;
		if(chosen_packet_arrived)
		  chosen_packet_arrived <= 1'b0;

        case(received_byte[1:0]) 
          2'b00: received_byte_data <= wdata[7:0];
          2'b01: received_byte_data <= wdata[15:8];
          2'b10: received_byte_data <= wdata[23:16];
          2'b11: received_byte_data <= wdata[31:24];
        endcase
      end
    end
  end

  ast_packet_integrity: assert property(chosen_packet_arrived |-> received_byte_data == chosen_byte_data);
  cov_chosen_byte_occurence: cover property(rnext ##[0:15] chosen_byte_flag);

  cov_chosen_byte_val0: cover property(chosen_byte == 4'h0);
  cov_chosen_byte_val1: cover property(chosen_byte == 4'h1);
  cov_chosen_byte_val2: cover property(chosen_byte == 4'h2);
  cov_chosen_byte_val3: cover property(chosen_byte == 4'h3);
  cov_chosen_byte_val4: cover property(chosen_byte == 4'h4);
  cov_chosen_byte_val5: cover property(chosen_byte == 4'h5);
  cov_chosen_byte_val15: cover property(chosen_byte == 4'hf);

  logic[3:0] free_byte_cnt;
  asm_max_free_byte_cnt: assume property(free_byte_cnt <= 4'hf);
  asm_min_free_byte_cnt: assume property(free_byte_cnt >= 4'h0);

  cov_all_byte_cnts: cover property(byte_cnt == 4'h0 && chosen_packet_arrived);
  cov_byte_cnts0: cover property(byte_cnt == 4'h0);
 	


endmodule
