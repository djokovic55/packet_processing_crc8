module checker_pp (
    input clk, reset,
    input pp_checker_en,
    pp_conf_port_intf.monitor pp_conf_port,
    mem_port_intf.monitor inmem_port_pp,
    pp_regs_port_intf.monitor pp_regs_port
);
    
	default 
	clocking @(posedge clk);
	endclocking

	default disable iff reset;


    logic pp_start;
    logic pp_irq;
    logic pp_pkt_crc_err;
    logic pp_pkt_ecc_corr;
    logic pp_pkt_ecc_uncorr;
    logic[3:0] pp_addr_hdr;
    logic[3:0] pp_pkt_byte_cnt;

    assign pp_start = pp_regs_port.pp_start;
    assign pp_irq = pp_regs_port.pp_irq;
    assign pp_pkt_crc_err = pp_regs_port.pp_pkt_crc_err;
    assign pp_pkt_ecc_corr = pp_regs_port.pp_pkt_ecc_corr;
    assign pp_pkt_ecc_uncorr = pp_regs_port.pp_pkt_ecc_uncorr;
    assign pp_addr_hdr = pp_regs_port.pp_addr_hdr;
    assign pp_pkt_byte_cnt = pp_regs_port.pp_pkt_byte_cnt;


	////////////////////////////////////////////////////////////////////////////////	
	//SECTION ECC CALCULATION IN PARSE TASK
	////////////////////////////////////////////////////////////////////////////////	
	logic[3:0] ecc_pp_calc_s;
	logic[7:0] ecc_data_in_pp_calc_s;
	logic ecc_msb_pp_calc_s;

	// In parser's checker based on received config, calculate ecc code and msb bit,
	// then upon write calculated data inside inmeme to prevent ecc errors

	// calculate ECC code from received header data
	assign ecc_pp_calc_s[0] = ecc_data_in_pp_calc_s[0] ^ ecc_data_in_pp_calc_s[1] ^ ecc_data_in_pp_calc_s[3] ^ ecc_data_in_pp_calc_s[4] ^ ecc_data_in_pp_calc_s[6];
	assign ecc_pp_calc_s[1] = ecc_data_in_pp_calc_s[0] ^ ecc_data_in_pp_calc_s[2] ^ ecc_data_in_pp_calc_s[3] ^ ecc_data_in_pp_calc_s[5] ^ ecc_data_in_pp_calc_s[6];
	assign ecc_pp_calc_s[2] = ecc_data_in_pp_calc_s[1] ^ ecc_data_in_pp_calc_s[2] ^ ecc_data_in_pp_calc_s[3] ^ ecc_data_in_pp_calc_s[7];
	assign ecc_pp_calc_s[3] = ecc_data_in_pp_calc_s[4] ^ ecc_data_in_pp_calc_s[5] ^ ecc_data_in_pp_calc_s[6] ^ ecc_data_in_pp_calc_s[7];

	// calculate ECC MSB bit do detect double+ errors
	assign ecc_msb_pp_calc_s = ecc_data_in_pp_calc_s[0] ^ ecc_data_in_pp_calc_s[1] ^ ecc_data_in_pp_calc_s[2] ^ ecc_data_in_pp_calc_s[3] ^ ecc_data_in_pp_calc_s[4] ^ ecc_data_in_pp_calc_s[5] ^ ecc_data_in_pp_calc_s[6] ^ ecc_data_in_pp_calc_s[7]; 

	////////////////////////////////////////////////////////////////////////////////	
	//SECTION CALCULATE ECC ERR CODE TO EXTRACT ECC ERRORS IN PARSE TASK
	////////////////////////////////////////////////////////////////////////////////	
	logic[7:0] ecc_data_in_pp_s;
	logic[3:0] ecc_pp_s;
	logic[3:0] ecc_err_code_pp_s;

	// In parser checker, read HEADER data and calculate err code, then based on received ECC MSB bit and generated ecc err code conclude error existence
	assign ecc_err_code_pp_s[0] = ecc_pp_s[0] ^ ecc_data_in_pp_s[0] ^ ecc_data_in_pp_s[1] ^ ecc_data_in_pp_s[3] ^ ecc_data_in_pp_s[4] ^ ecc_data_in_pp_s[6];
	assign ecc_err_code_pp_s[1] = ecc_pp_s[1] ^ ecc_data_in_pp_s[0] ^ ecc_data_in_pp_s[2] ^ ecc_data_in_pp_s[3] ^ ecc_data_in_pp_s[5] ^ ecc_data_in_pp_s[6];
	assign ecc_err_code_pp_s[2] = ecc_pp_s[2] ^ ecc_data_in_pp_s[1] ^ ecc_data_in_pp_s[2] ^ ecc_data_in_pp_s[3] ^ ecc_data_in_pp_s[7];
	assign ecc_err_code_pp_s[3] = ecc_pp_s[3] ^ ecc_data_in_pp_s[4] ^ ecc_data_in_pp_s[5] ^ ecc_data_in_pp_s[6] ^ ecc_data_in_pp_s[7];

	////////////////////////////////////////////////////////////////////////////////	
	// PARSER'S BYTE COUNT ASSUMTION LOGIC
	// Based on defined hdr_addr, byte count must set so that their sum does not exceed h'13
	////////////////////////////////////////////////////////////////////////////////	

	logic[3:0] pp_byte_cnt;
	asm_pp_byte_cnt_stability: assume property($stable(pp_byte_cnt));
	asm_pp_addr_deadend: assume property(pp_byte_cnt + pp_conf_port_intf.pp_addr_hdr + 3 <= 14'h12);
	logic inmem_pp_we_s;
	logic[31:0] inmem_pp_data_s;

	////////////////////////////////////////////////////////////////////////////////	
	//IMPORTANT Check CRC calculation
	////////////////////////////////////////////////////////////////////////////////	

	// Read data from memory after pp_start
	logic[7:0] data_in_s;
	logic[7:0] crc_mid_result_reg, crc_mid_result_next;
	logic[7:0] crc_out_s;

	logic[3:0] crc_cnt_reg, crc_cnt_next;
	logic[7:0] crc_ext_reg, crc_ext_next;
	logic[7:0] crc_calc_reg, crc_calc_next;
	logic[3:0] byte_cnt_reg, byte_cnt_next;

	logic[13:0] addr_free;
	logic[13:0] addr_reg, addr_next;

	logic crc_err_reg, crc_err_next;
	logic corr_err_irq_reg, corr_err_irq_reg2;
	logic corr_err_irq_pulse;
	logic ecc_corr_err_pp_reg, ecc_corr_err_pp_next;
	logic ecc_uncorr_err_pp_reg, ecc_uncorr_err_pp_next;

	// CRC calc FSM
	typedef enum {IDLE, HEADER_READ, CRC_CALC, COMPARE_CRC} State;
	State state_reg, state_next;

	// detect single error irq edge
	always_ff @(posedge clk) begin
	 	if(reset || pp_irq) begin
			corr_err_irq_reg <= 1'b0;
			corr_err_irq_reg2 <= 1'b0;
		end
		else begin
			if(pp_pkt_ecc_corr)
				corr_err_irq_reg <= 1'b1;

			corr_err_irq_reg2 <= corr_err_irq_reg;
		end
	end
	assign corr_err_irq_pulse = !corr_err_irq_reg2 && corr_err_irq_reg;

	// seq logic
	always_ff @(posedge clk) begin
		if(reset) begin
			state_reg <= IDLE;
			crc_calc_reg <= '0;
			crc_cnt_reg <=  '0;
			crc_ext_reg <=  '0;
			crc_calc_reg <=  '0;
			byte_cnt_reg <=  '0;
			addr_reg <=  '0;
			crc_err_reg <= 1'b0;

			ecc_corr_err_pp_reg <= 1'b0;
			ecc_uncorr_err_pp_reg <= 1'b0;

		end
		else begin
			state_reg <= state_next;
			crc_cnt_reg <=  crc_cnt_next;
			crc_ext_reg <=  crc_ext_next;
			crc_calc_reg <=  crc_calc_next;
			byte_cnt_reg <=  byte_cnt_next;
			addr_reg <=  addr_next;
			crc_err_reg <= crc_err_next;

			ecc_corr_err_pp_reg <= ecc_corr_err_pp_next;
			ecc_uncorr_err_pp_reg <= ecc_uncorr_err_pp_next ;
		end
	end

	// comb logic
	always_comb begin
	// defaults
		data_in_s = '0;
		inmem_pp_we_s = '0;
		state_next = state_reg;
		addr_next = addr_reg;
		byte_cnt_next = byte_cnt_reg;
		crc_cnt_next = crc_cnt_reg;
		crc_ext_next = crc_ext_reg;
		crc_calc_next = crc_calc_reg;
		crc_err_next = crc_err_reg;

		ecc_corr_err_pp_next = ecc_corr_err_pp_reg;
		ecc_uncorr_err_pp_next = ecc_uncorr_err_pp_reg;

		// single error interrupt, cancel current execution
		// start again and reset everything with correct byte count data
		if(corr_err_irq_pulse) begin

			byte_cnt_next = pp_pkt_byte_cnt;
			addr_next = pp_addr_hdr + 2;
			crc_cnt_next = '0;
			crc_ext_next = '0;
			crc_calc_next = '0;
			crc_err_next = '0;

			state_next = CRC_CALC;
		end 
		else begin

			case(state_reg)
				IDLE: begin 
					crc_cnt_next = '0;
					if(pp_irq) begin
						ecc_corr_err_pp_next = '0;
						ecc_uncorr_err_pp_next = '0;
						crc_err_next = '0;
					end

					if(pp_start && pp_checker_en) begin
						crc_err_next = '0;
						addr_next = pp_addr_hdr;
						state_next = HEADER_READ;
					end else
						state_next = IDLE;
				end
				//
				HEADER_READ: begin
					// calculate correct ecc
					// pkt_type from memory
					ecc_data_in_pp_calc_s[7:4] = inmem_port_pp.data_o[11:8];
					// byte_cnt from free variable
					ecc_data_in_pp_calc_s[3:0] = pp_byte_cnt;

					// enable write
					inmem_pp_we_s = 4'b1111;
					// write byte cnt data in inmem, preserve previous data
					// IMPORTANT when we is held, tool can change any other bit as addition to byte cnt change
					// Here correct ecc code must be inserted

					// Msb bytes which represent data following header
					inmem_pp_data_s[31:8] = inmem_port_pp.data_o[31:16];
					// Sop
					inmem_pp_data_s[15:13] = inmem_port_pp.data_o[15:13];
					// ECC Msb
					inmem_pp_data_s[12] = ecc_msb_pp_calc_s;
					// pkt type
					inmem_pp_data_s[11:8] = inmem_port_pp.data_o[11:8];
					// byte cnt
					inmem_pp_data_s[7:4] = pp_byte_cnt;
					// ecc code 
					inmem_pp_data_s[3:0] = ecc_pp_calc_s;

					// store free data in checker
					byte_cnt_next = pp_byte_cnt;
					// increment address to start reading data
					addr_next = addr_reg + 2;
					// Check for errors and compare with parser's conclusion
					// BUG byte count info must come from free variable
					ecc_data_in_pp_s[7:4] = inmem_port_pp.data_o[11:8];
					ecc_data_in_pp_s[3:0] = pp_byte_cnt;
					ecc_pp_s = inmem_port_pp.data_o[3:0];

					if(ecc_err_code_pp_s != '0) begin
						// received ecc msb bit
						if(inmem_port_pp.data_o[12:12])
							ecc_corr_err_pp_next = 1'b1;
						else 
							ecc_uncorr_err_pp_next = 1'b1;
					end 
					state_next = CRC_CALC;
				end
				CRC_CALC: begin
					data_in_s = inmem_port_pp.data_o[7:0];
					crc_cnt_next = crc_cnt_reg + 1;
					// increment only if staying in current state
					// addr_next = addr_reg + 1;
					// store CRC
					// BUG Dead-end 
					// if(crc_cnt_reg == byte_cnt_reg)
					// BUG WRONG addr_reg, +2 must be added to skip header bytes
					if(addr_reg == pp_addr_hdr + byte_cnt_reg + 2)
						crc_calc_next = crc_out_s;

					//if(crc_cnt_reg == byte_cnt_reg + 1) begin
					//BUG Wrong CRC addr, +3 rather than +1
					if(addr_reg == pp_addr_hdr + byte_cnt_reg + 3) begin
						crc_ext_next = inmem_port_pp.data_o[7:0];
						state_next = COMPARE_CRC;
					end 
					else begin
						addr_next = addr_reg + 1;
						state_next = CRC_CALC;
					end
				end
				COMPARE_CRC: begin
					if(crc_ext_reg == crc_calc_reg) begin
						crc_err_next = 1'b0;
					end else
						crc_err_next = 1'b1;

					state_next = IDLE;
				end
			endcase
		end
	end 
	////////////////////////////////////////////////////////////////////////////////	
	// Block for crc byte calculation
	////////////////////////////////////////////////////////////////////////////////	
	crc_chk_calc pp_crc_check(
		.crc_in(crc_mid_result_reg),
		.data_in(data_in_s),
		.crc_out(crc_out_s));

	// Mid-result crc register block
	always @(posedge clk) begin
		if(reset)
			crc_mid_result_reg <= '0;
		else if(pp_start || corr_err_irq_pulse) 
			crc_mid_result_reg <= '0;
		else
			crc_mid_result_reg <= crc_out_s;
	end

    
	// Asssert correct CRC
	// It is important to have pp_checker_en precondition because that is the condition under which inmem_addr gets its value from parser block

	ast_pp_crc_err_coverage:                        assert property(##1 (pp_checker_en && pp_irq && $past(pp_pkt_crc_err) && !pp_pkt_ecc_uncorr && !pp_pkt_ecc_corr) |-> crc_err_reg);
	ast_pp_crc_no_err_coverage:                     assert property(pp_checker_en && pp_irq && $past(!pp_pkt_crc_err) && !pp_pkt_ecc_uncorr && !pp_pkt_ecc_corr |-> !crc_err_reg);

	// ast_pp_crc_err_when_ecc_err_exists_coverage:    assert property(pp_checker_en && pp_irq && $past(pp_pkt_crc_err) && !pp_pkt_ecc_uncorr && pp_pkt_ecc_corr |-> crc_err_reg);
	ast_pp_crc_err_when_ecc_err_exists_coverage:    assert property(pp_checker_en && pp_irq && $past(pp_pkt_crc_err) && !pp_pkt_ecc_uncorr && $past(pp_pkt_ecc_corr) |-> crc_err_reg);
	ast_pp_crc_no_err_when_ecc_err_exists_coverage: assert property(pp_checker_en && pp_irq && $past(!pp_pkt_crc_err) && !pp_pkt_ecc_uncorr && $past(pp_pkt_ecc_corr) |-> !crc_err_reg);

	ast_pp_ecc_corr_err_coverage:                   assert property(pp_checker_en && pp_pkt_ecc_corr |-> ecc_corr_err_pp_reg);
	ast_pp_ecc_uncorr_err_coverage:                 assert property(pp_checker_en && pp_pkt_ecc_uncorr |-> ecc_uncorr_err_pp_reg);

	// Parser checker is driver to these signals
    // assign inmem_port_pp.addr = addr_reg;
	asm_inmem_addr: assume property(inmem_port_pp.addr == addr_reg);
    // assign inmem_port_pp.we = inmem_pp_we_s;
	asm_inmem_we: assume property(inmem_port_pp.we == inmem_pp_we_s);
    // assign inmem_port_pp.data_i = inmem_pp_data_s;
	asm_inmem_data_i: assume property(inmem_port_pp.data_i == inmem_pp_data_s);

	// Check pp registers 

	ast_reg_pp_addr_hdr_lv4_help_high:              assert property(pp_regs_port.pp_start |-> pp_regs_port.pp_addr_hdr == pp_conf_port.pp_addr_hdr);
	ast_reg_pp_ignore_ecc_err_lv4_help_high:        assert property(pp_regs_port.pp_start |-> pp_regs_port.pp_ignore_ecc_err == pp_conf_port.pp_ignore_ecc_err);


endmodule