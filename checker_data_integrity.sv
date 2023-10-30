
checker checker_data_integrity(
  clk,
  reset,

  byte_cnt,
  data_sel,

  wdata,
  wvalid,
  wlast,
  wready, 

  rdata,
  rlast,
  rvalid,
  rready

);

	default clocking @(posedge clk);
	endclocking

	default disable iff reset;

  reg[4:0] wpulse_cnt; 
  reg[3:0] rpulse_cnt;

  // handshake flags
  logic wnext = wvalid && wready;
  logic rnext = rvalid && rnext;

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

  asm_chosen_byte_op0: assume property(disable iff(reset && (data_sel != 4'h0))
    chosen_byte <= byte_cnt[3:2]);

  asm_chosen_byte_op1: assume property(disable iff(reset && (data_sel != 4'h1))
    chosen_byte <= byte_cnt[3:2] && chosen_byte[0] == 1'b0);
  
  asm_chosen_byte_op1: assume property(disable iff(reset && (data_sel != 4'h2))
    chosen_byte <= byte_cnt);

  reg[7:0] chosen_byte_data;
  const logic[3:0] OP0 = 4'h0;
  const logic[3:0] OP1 = 4'h1;
  const logic[3:0] OP2 = 4'h2;

  // store chosen byte data
  always @(posedge clk) begin
    if(reset) begin
      chosen_byte_data <= '0; 
    end
    else begin
      case(data_sel) 
        OP0: begin
          if(chosen_byte[3:2] == rpulse_cnt)
            chosen_byte_data <= rdata[7:0];
        end
        OP1: begin
          if(chosen_byte[3:2] == rpulse_cnt) begin
            case(chosen_byte[0]) 
              1'b0: chosen_byte_data <= rdata[7:0];
              1'b1: chosen_byte_data <= rdata[15:8];
            endcase
          end
        end
        OP2: begin
          if(chosen_byte[3:2] == rpulse_cnt) begin
            case(chosen_byte[1:0]) 
              2'b00: chosen_byte_data <= rdata[7:0];
              2'b01: chosen_byte_data <= rdata[15:8];
              2'b10: chosen_byte_data <= rdata[23:16];
              2'b11: chosen_byte_data <= rdata[31:24];
            endcase
          end
        end
      endcase
    end
  end

 //////////////////////////////////////////////////////////////////////////////// 
 // Packet OUT interface
 //////////////////////////////////////////////////////////////////////////////// 

  logic received_byte; 
  always @(posedge clk) begin
    if(reset) begin
      received_byte <= '0;
    end
    else begin
      case(data_sel) 
        OP1: received_byte <= ((chosen_byte[3:2] * 2) + chosen_byte[0] + 2);
        default: received_byte <= (chosen_byte + 2); 
      endcase
    end
  end

  // Indication that chosen packet arrived at the output
  logic chosen_packet_arrived;

  // store received data byte
  always @(posedge clk) begin
    if(reset) begin
      received_byte_data <= '0; 
      chosen_packet_arrived <= 1'b0;
    end
    else begin
      if(received_byte[4:2] == rpulse_cnt) begin

        chosen_packet_arrived <= 1'b1;

        case(received_byte[1:0]) 
          2'b00: received_byte_data <= rdata[7:0];
          2'b01: received_byte_data <= rdata[15:8];
          2'b10: received_byte_data <= rdata[23:16];
          2'b11: received_byte_data <= rdata[31:24];
        endcase
      end
    end
  end

  ast_packet_integrity: assert property(chosen_packet_arrived |-> received_byte_data == chosen_byte_data);


endchecker