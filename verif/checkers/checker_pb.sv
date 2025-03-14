module checker_pb (

    input clk, reset,
    input pb_checker_en,
    pb_conf_port_intf.monitor pb_conf_port,
    mem_port_intf.monitor inmem_port_pb,
    mem_port_intf.monitor outmem_port_pb,
    pb_regs_port_intf.monitor pb_regs_port
);

	default 
	clocking @(posedge clk);
	endclocking
	default disable iff reset;

	logic pb_start;
	logic pb_irq_top;

	logic pb_crc_en;
	logic[7:0] pb_crc_val;
	logic[31:0] pb_addr_in;
	logic[3:0] pb_data_sel;
	logic[3:0] pb_byte_cnt;
	logic[31:0] pb_addr_out;

	logic[31:0] inmem_data_b_o;
	logic[31:0] outmem_data_b_o;

    assign pb_start = pb_regs_port.pb_start;
    assign pb_irq_top = pb_regs_port.pb_irq;

    assign pb_crc_en = pb_conf_port.pb_crc_en;
    assign pb_crc_val = pb_conf_port.pb_crc_val;
    assign pb_addr_in = pb_conf_port.pb_addr_in;
    assign pb_data_sel = pb_conf_port.pb_data_sel;
    assign pb_byte_cnt = pb_conf_port.pb_byte_cnt;
    assign pb_addr_out = pb_conf_port.pb_addr_out;

    assign inmem_data_b_o = inmem_port_pb.data_o;
    assign outmem_data_b_o = outmem_port_pb.data_o;

	logic[3:0] chosen_byte; // CHECKER_INPUT chosen_byte

	asm_chosen_byte_stable:           assume property($stable(chosen_byte));
	asm_chosen_byte_op0:              assume property(disable iff(reset) pb_data_sel == 4'h0 |-> chosen_byte <= pb_byte_cnt && chosen_byte[1:0] == 2'b0);
	asm_chosen_byte_op1:              assume property(disable iff(reset) pb_data_sel == 4'h1 |-> chosen_byte <= pb_byte_cnt && chosen_byte[1] == 1'b0);
	asm_chosen_byte_op2:              assume property(disable iff(reset) pb_data_sel == 4'h2 |-> chosen_byte <= pb_byte_cnt);

	logic[13:0] inmem_addr_di;
	logic[13:0] inmem_addr_crc;
	logic[13:0] outmem_addr_di_crc;

	typedef enum {IDLE_DI, CHOOSE_BYTE, CRC_CALC_DI, RECEIVE_BYTE, COMPARE_CRC_DI} di_State;
	di_State di_state_reg, di_state_next;

    reg[7:0] chosen_byte_data, chosen_byte_data_next;
    logic chosen_byte_flag;
    const logic[3:0] OP0 = 4'h0;
    const logic[3:0] OP1 = 4'h1;
    const logic[3:0] OP2 = 4'h2;

	logic[13:0] chosen_byte_addr, chosen_byte_addr_reg; // CHECKER_OUTPUT inmem addr for di check
	logic[13:0] di_crc_addr_reg, di_crc_addr_next; // CHECKER_OUTPUT inmem addr for crc check
	logic[13:0] received_byte_addr; // CHECKER_OUTPUT outmem addr for both di and crc check

	logic di_err; // Data integrity error flag

    logic[4:0] received_byte; 
    logic[7:0] received_byte_data, received_byte_data_next;

	// crc check signals
	logic[7:0] di_crc_mid_result_reg;
	logic[7:0] di_crc_data_in_s;
	logic[7:0] di_crc_out_s;
	// logic[7:0] di_crc_ext_reg, di_crc_ext_next;
	logic[7:0] di_crc_calc_reg, di_crc_calc_next;
	logic di_crc_err_s;
	logic[13:0] crc_addr_s;
	logic[7:0] byte_cnt;

	logic op1_data_cnt_reg, op1_data_cnt_next;

	////////////////////////////////////////////////////////////////////////////////
	// Data_sel dependent info
	////////////////////////////////////////////////////////////////////////////////
    always_comb begin
        case(pb_data_sel) 
            OP0: begin 
                // address of received byte
                received_byte <= (chosen_byte[3:2] + 2);
                // crc position
                crc_addr_s <= (pb_byte_cnt[3:2] + 3);
                // byte count
                byte_cnt <= (pb_byte_cnt[3:2]);
            end
            OP1: begin
                received_byte <= ((chosen_byte[3:2] * 2) + chosen_byte[0] + 2);
                crc_addr_s <= ((pb_byte_cnt[3:2] * 2) + (pb_byte_cnt[1] || pb_byte_cnt[0]) + 3);
                byte_cnt <= ((pb_byte_cnt[3:2] * 2) + (pb_byte_cnt[1] || pb_byte_cnt[0]));
            end
            default: begin 
                received_byte <= (chosen_byte + 2); 
                crc_addr_s <= (pb_byte_cnt + 3); 
                byte_cnt <= pb_byte_cnt;
            end
        endcase
    end

	////////////////////////////////////////////////////////////////////////////////
	// CRC calc block
	////////////////////////////////////////////////////////////////////////////////

	// Mid-result crc register block
	always @(posedge clk) begin
		if(reset)
			di_crc_mid_result_reg <= '0;
		else if(pb_start) 
			di_crc_mid_result_reg <= '0;
		else
			di_crc_mid_result_reg <= di_crc_out_s;
	end

	// Block for crc byte calculation during build phase
	crc_chk_calc pb_crc_check(
		.crc_in(di_crc_mid_result_reg),
		.data_in(di_crc_data_in_s),
		.crc_out(di_crc_out_s));
	////////////////////////////////////////////////////////////////////////////////

	// registers
	always_ff @(posedge clk) begin
		if(reset) begin
			di_state_reg <= IDLE_DI;
			chosen_byte_data <= '0;
			received_byte_data <= '0;
			di_crc_addr_reg <= '0;
			di_crc_calc_reg <=  '0;
			chosen_byte_addr_reg <=  '0;

			op1_data_cnt_reg <= '0;
		end
		else begin
			di_state_reg <= di_state_next;
			chosen_byte_data <= chosen_byte_data_next;
			received_byte_data <= received_byte_data_next;
			di_crc_addr_reg <= di_crc_addr_next;
			di_crc_calc_reg <=  di_crc_calc_next;
			chosen_byte_addr_reg <=  chosen_byte_addr;


			op1_data_cnt_reg <= op1_data_cnt_next;
		end
	end

	// crc calculation check logic will be embedded into this FSM
	// received_byte_addr is used to read crc_ext from outmem
    `ifdef ENV_TEST

    `else
	always_comb begin
		// defaults
		di_state_next = di_state_reg;
		chosen_byte_data_next = chosen_byte_data;
		received_byte_data_next = received_byte_data;
		chosen_byte_addr = chosen_byte_addr_reg;
		received_byte_addr = '0;
		di_err = '0;
		// default data for crc calculation
		di_crc_data_in_s = '0;

		di_crc_addr_next = di_crc_addr_reg;
		// di_crc_ext_next = di_crc_ext_reg;
		di_crc_calc_next = di_crc_calc_reg;
		di_crc_err_s = 1'b0;

		op1_data_cnt_next = op1_data_cnt_reg;
        // PORT assignment 
        inmem_addr_di = chosen_byte_addr_reg;
        // !!! BUG !!! this was missing -> inmem_addr_crc was a free net
        inmem_addr_crc = di_crc_addr_reg;
        // ALWAYS STORE CHOSEN_BYTE_DATA BECAUSE ADDRESS SHOULD REMAIN STABLE
        chosen_byte_data_next = inmem_data_b_o; // CHECKER_INPUT inmem_data_b_o

		case(di_state_reg)
			IDLE_DI: begin 
				// starting address for crc data calculation
				di_crc_addr_next = pb_addr_in; // CHECKER_INPUT pb_addr_in
				op1_data_cnt_next = 0;

				if(pb_start && pb_checker_en) begin
					di_state_next = CHOOSE_BYTE;
				end else
					di_state_next = IDLE_DI;
			end
			CHOOSE_BYTE: begin
				chosen_byte_addr = pb_addr_in + chosen_byte;
                inmem_addr_di = chosen_byte_addr;
				chosen_byte_data_next = inmem_data_b_o; // CHECKER_INPUT inmem_data_b_o
				// if crc calc disabled, use predefined value
				if(pb_crc_en)
					di_state_next = CRC_CALC_DI;
				else begin
					di_crc_calc_next = pb_crc_val;
					di_state_next = RECEIVE_BYTE;
				end
			end
			CRC_CALC_DI: begin

				// crc data available in this state
				di_crc_data_in_s = inmem_data_b_o;

				// address increment logic differs based on data_sel
				case(pb_data_sel) 
					OP0: begin 
						di_crc_addr_next = di_crc_addr_reg + 4;
					end
					OP1: begin
						op1_data_cnt_next = !op1_data_cnt_reg;
						//BUG what if pb_addr_in[1] = 1? It will skip the next byte
						if(op1_data_cnt_reg == 1'b0) begin
							di_crc_addr_next = di_crc_addr_reg + 1;
						end
						else begin
							//skip 2 msb bytes and target lsb in new beat
							di_crc_addr_next = di_crc_addr_reg + 3;
						end
					end
					default: begin 
						di_crc_addr_next = di_crc_addr_reg + 1;
					end
				endcase

				//store CRC
				// means last data byte was read and therefore crc is ready
				// BUG full data byte info (pb_byte_cnt) has to be used because some bytes are skipped, but still their location is beyond newly calculated byte_cnt
				// BUG deadlock, for op1 it can jump over pb_addr_in + pb_byte_cnt so it was necessary to check if the next address will be > not ==
				if(di_crc_addr_next > pb_addr_in + pb_byte_cnt) begin
					// store calculated CRC
					di_crc_calc_next = di_crc_out_s;
					di_state_next = RECEIVE_BYTE;
				end
				else begin
					di_state_next = CRC_CALC_DI;
				end
			end
			RECEIVE_BYTE: begin
				received_byte_addr = pb_addr_out + received_byte; // CHECKER_INPUT pb_addr_out
				if(pb_irq_top) begin
					received_byte_data_next = outmem_data_b_o; // CHECKER_INPUT outmem_data_b_o
                    // reset reg
                    chosen_byte_addr = '0;
					if(chosen_byte_data != received_byte_data_next)
						di_err = 1'b1; // CHOOSE_OUTPUT di_err

					di_state_next = COMPARE_CRC_DI;
				end else
					di_state_next = RECEIVE_BYTE;
			end
			// In this state crc byte is extracted
			// Outmem we is always disabled, 
			// no fear that written crc value will ever be overwritten by the tool
			COMPARE_CRC_DI: begin
				// crc address in outgoing memory of a built packet
				//BUG byte_cnt depens on data_sel
				received_byte_addr = pb_addr_out + crc_addr_s; // 2 for header, 1 for crc
				// check crc
				if(di_crc_calc_reg != outmem_data_b_o[7:0])
					di_crc_err_s = 1'b1; // CHOOSE_OUTPUT di_crc_err_s

				di_state_next = IDLE_DI;
			end
		endcase
	end 
    `endif

    logic[31:0] inmem_addr;

	// Port assignments
    assign inmem_addr = di_state_reg == CRC_CALC_DI ? inmem_addr_crc : inmem_addr_di;
    asm_inmem_adrr: assume property(inmem_port_pb.addr == inmem_addr);
	assign outmem_addr_di_crc = received_byte_addr;
    asm_outmem_addr: assume property(outmem_port_pb.addr == outmem_addr_di_crc);


	cov_no_zero_data: cover property(chosen_byte_data != '0);

	ast_data_integrity_coverage:                            assert property(pb_checker_en |-> !di_err);
	ast_data_integrity_crc_coverage:                        assert property(pb_checker_en |-> !di_crc_err_s);

	// Check pb registers
	ast_reg_pb_addr_in_lv4_help_high:              assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_addr_in == pb_conf_port.pb_addr_in);
	ast_reg_pb_byte_cnt_lv4_help_high:             assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_byte_cnt == pb_conf_port.pb_byte_cnt);
	ast_reg_pb_pkt_type_lv4_help_high:             assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_pkt_type == pb_conf_port.pb_pkt_type);
	ast_reg_pb_ecc_en_lv4_help_high:               assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_ecc_en == pb_conf_port.pb_ecc_en);
	ast_reg_pb_crc_en_lv4_help_high:               assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_crc_en == pb_conf_port.pb_crc_en);
	ast_reg_pb_ins_ecc_err_lv4_help_high:          assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_ins_ecc_err == pb_conf_port.pb_ins_ecc_err);
	ast_reg_pb_ins_crc_err_lv4_help_high:          assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_ins_crc_err == pb_conf_port.pb_ins_crc_err);
	ast_reg_pb_ecc_val_lv4_help_high:              assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_ecc_val == pb_conf_port.pb_ecc_val);
	ast_reg_pb_crc_val_lv4_help_high:              assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_crc_val == pb_conf_port.pb_crc_val);
	ast_reg_pb_sop_val_lv4_help_high:              assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_sop_val == pb_conf_port.pb_sop_val);
	ast_reg_pb_data_sel_lv4_help_high:             assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_data_sel == pb_conf_port.pb_data_sel);
	ast_reg_pb_addr_out_lv4_help_high:             assert property(pb_regs_port.pb_start |-> pb_regs_port.pb_addr_out == pb_conf_port.pb_addr_out);

endmodule