
module  checker_di_top(
  input clk,
  input reset,
  input checker_en,

  input[7:0] chosen_byte,

  input[31:0] pb_addr_in,
  input[31:0] inmem_data_b_o,

  input[31:0] pb_addr_out,
  input[31:0] outmem_data_b_o,

  output[13:0] inmem_addr_di,
  output[13:0] inmem_addr_crc,
  output[13:0] outmem_addr_di_crc,
	);
	
  default 
  clocking @(posedge clk);
  endclocking

  default disable iff reset;

	// Port assignments
	assign inmem_addr_di = chosen_byte_addr;
	assign inmem_addr_crc = di_crc_addr_reg;
	assign outmem_addr_di_crc = received_byte_addr;

	typedef enum {IDLE_DI, CHOOSE_BYTE, CRC_CALC_DI, RECEIVE_BYTE, COMPARE_CRC_DI} di_State;
	di_State di_state_reg, di_state_next;

  reg[7:0] chosen_byte_data, chosen_byte_data_next;
  logic chosen_byte_flag;
  const logic[3:0] OP0 = 4'h0;
  const logic[3:0] OP1 = 4'h1;
  const logic[3:0] OP2 = 4'h2;

	logic[13:0] chosen_byte_addr; // CHECKER_OUTPUT inmem addr for di check
	logic[13:0] di_crc_addr_reg, di_crc_addr_next; // CHECKER_OUTPUT inmem addr for crc check
	logic[13:0] received_byte_addr; // CHECKER_OUTPUT outmem addr for both di and crc check

	logic di_err; // Data integrity error flag

  logic[4:0] received_byte; 
  reg[7:0] received_byte_data, received_byte_data_next;

	// crc check signals
	reg[7:0] di_crc_mid_result_reg;
	logic[7:0] di_crc_out_s;
	// logic[7:0] di_crc_ext_reg, di_crc_ext_next;
	logic[7:0] di_crc_calc_reg, di_crc_calc_next;
	logic di_crc_err_s;


  always_comb begin
		case(pb_data_sel) 
			OP0: received_byte <= (chosen_byte[3:2] + 2);
			OP1: received_byte <= ((chosen_byte[3:2] * 2) + chosen_byte[0] + 2);
			default: received_byte <= (chosen_byte + 2); 
		endcase
  end

	// Mid-result crc register block
	always @(posedge clk) begin
		if(reset)
			di_crc_mid_result_reg <= '0;
		else if(pb0_start_top) 
			di_crc_mid_result_reg <= '0;
		else
			di_crc_mid_result_reg <= di_crc_out_s;
	end

	// Block for crc byte calculation during build phase
	crc_chk_calc pb_crc_check(
		.crc_in(di_crc_mid_result_reg),
		.data_in(inmem_data_b_o),
		.crc_out(di_crc_out_s));

	// registers
	always_ff @(posedge clk) begin
		if(reset) begin
			di_state_reg <= IDLE_DI;
			chosen_byte_data <= '0;
			received_byte_data <= '0;
			di_crc_addr_reg <= '0;
			// di_crc_ext_reg <=  '0;
			di_crc_calc_reg <=  '0;
		end
		else begin
			di_state_reg <= di_state_next;
			chosen_byte_data <= chosen_byte_data_next;
			received_byte_data <= received_byte_data_next;
			di_crc_addr_reg <= di_crc_addr_next;
			// di_crc_ext_reg <=  di_crc_ext_next;
			di_crc_calc_reg <=  di_crc_calc_next;
		end
	end

	// crc calculation check logic will be embedded into this FSM
	// received_byte_addr is used to read crc_ext from outmem

	always_comb begin
		// defaults
		di_state_next <= di_state_reg;
		chosen_byte_data_next <= chosen_byte_data;
		received_byte_data_next <= received_byte_data;
		chosen_byte_addr <= '0;
		received_byte_addr <= '0;
		di_err <= '0;

		di_crc_addr_next <= di_crc_addr_reg;
		// di_crc_ext_next <= di_crc_ext_reg;
		di_crc_calc_next <= di_crc_calc_reg;
		di_crc_err_s <= 1'b0;

		case(di_state_reg)
			IDLE_DI: begin 
				di_crc_addr_next <= pb_addr_in; // CHECKER_INPUT pb_addr_in

				if(pb0_start_top && checker_en) begin
					di_state_next <= CHOOSE_BYTE;
				end else
					di_state_next <= IDLE_DI;
			end
			CHOOSE_BYTE: begin
				chosen_byte_addr <= pb_addr_in + chosen_byte;
				chosen_byte_data_next <= inmem_data_b_o; // CHECKER_INPUT inmem_data_b_o

				di_state_next <= CRC_CALC_DI;
			end
			CRC_CALC_DI: begin
				di_crc_addr_next <= di_crc_addr_reg + 1;

				//store CRC
				if(di_crc_addr_reg == pb_addr_in + pb_byte_cnt) begin
					di_crc_calc_next <= di_crc_out_s;

					di_state_next <= RECEIVE_BYTE;
				end

				di_state_next <= CRC_CALC_DI;
			end
			RECEIVE_BYTE: begin
				if(pb0_irq_top) begin
					received_byte_addr <= pb_addr_out + received_byte; // CHECKER_INPUT pb_addr_out
					received_byte_data_next <= outmem_data_b_o; // CHECKER_INPUT outmem_data_b_o
					if(chosen_byte_data != received_byte_data_next)
						di_err <= 1'b1; // CHOOSE_OUTPUT di_err
						di_state_next <= COMPARE_CRC_DI;
				end else
					di_state_next <= RECEIVE_BYTE;
			end
			// In this state crc byte is extracted
			// Outmem we is always disabled, 
			// no fear that written crc value will ever be overwritten by the tool
			COMPARE_CRC_DI: begin
				// crc address in outgoing memory of a built packet
				received_byte_addr <= pb_addr_out + pb_byte_cnt + 3; // 2 for header, 1 for crc
				// check crc
				if(di_crc_calc_reg != outmem_data_b_o)
					di_crc_err_s <= 1'b1; // CHOOSE_OUTPUT di_crc_err_s

				di_state_next <= IDLE_DI;
			end
		endcase
	end 

endmodule
