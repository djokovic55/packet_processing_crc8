
module  checker_top(
	////////////////////////////////////////////////////////////////////////////////
	// Interface
	////////////////////////////////////////////////////////////////////////////////

  input clk,
  input reset,

  // ex_reg top interface 

	////////////////////////////////////////////////////////////////////////////////
	// Build task configuration
	////////////////////////////////////////////////////////////////////////////////
  output pb_irq,
  output[31:0] pb_addr_in, // assumed
  output[3:0] pb_byte_cnt,// assumed
  output[3:0] pb_pkt_type,
  output pb_ecc_en,
  output pb_crc_en,
  output pb_ins_ecc_err,
  output pb_ins_crc_err,
  output[3:0] pb_ecc_val,
  output[7:0] pb_crc_val,
  output[2:0] pb_sop_val,
  output[3:0] pb_data_sel,// assumed
  output[31:0] pb_addr_out,// assumed

	////////////////////////////////////////////////////////////////////////////////
	// Parse task configuration
	////////////////////////////////////////////////////////////////////////////////
  output pp_irq,
  output[31:0] pp_addr_hdr,
	output pp_ignore_ecc_err,

	////////////////////////////////////////////////////////////////////////////////
  // Inmem port B top interface, used for memory configuration
	////////////////////////////////////////////////////////////////////////////////
  output inmem_en_b_i,
  output[31:0] inmem_data_b_i,
  output[13:0] inmem_addr_b_i,
  output inmem_we_b_i,
  input[31:0] inmem_data_b_o,

	////////////////////////////////////////////////////////////////////////////////
  // Outmem port B top interface, memory read only
	////////////////////////////////////////////////////////////////////////////////
  output outmem_en_b_i,
  output[31:0] outmem_data_b_i,
  output[13:0] outmem_addr_b_i,
  output outmem_we_b_i,
  input[31:0] outmem_data_b_o,

	////////////////////////////////////////////////////////////////////////////////
	// Controller's status signal
	////////////////////////////////////////////////////////////////////////////////
	input cont_busy_top,

	////////////////////////////////////////////////////////////////////////////////
  // regs top interface
	////////////////////////////////////////////////////////////////////////////////
  input pb0_start_top,
  input pb0_busy_top,
  input pb0_irq_top,
  input[31:0] pb0_addr_in_top,
  input[3:0] pb0_byte_cnt_top,
  input[3:0] pb0_pkt_type_top,
  input pb0_ecc_en_top,
  input pb0_crc_en_top,
  input[1:0] pb0_ins_ecc_err_top,
  input pb0_ins_crc_err_top,
  input[3:0] pb0_ecc_val_top,
  input[7:0] pb0_crc_val_top,
  input[2:0] pb0_sop_val_top,
  input[3:0] pb0_data_sel_top,
  input[31:0] pb0_addr_out_top,

  input pb1_start_top,
  input pb1_busy_top,
  input pb1_irq_top,
  input[31:0] pb1_addr_in_top,
  input[3:0] pb1_byte_cnt_top,
  input[3:0] pb1_pkt_type_top,
  input pb1_ecc_en_top,
  input pb1_crc_en_top,
  input[1:0] pb1_ins_ecc_err_top,
  input pb1_ins_crc_err_top,
  input[3:0] pb1_ecc_val_top,
  input[7:0] pb1_crc_val_top,
  input[2:0] pb1_sop_val_top,
  input[3:0] pb1_data_sel_top,
  input[31:0] pb1_addr_out_top,

  input pp_start_top,
  input pp_busy_top,
  input pp_irq_top,
  input[31:0] pp_addr_hdr_top,
  input pp_ignore_ecc_err_top,
  input pp_pkt_ecc_corr_top,
  input pp_pkt_ecc_uncorr_top,
  input pp_pkt_crc_err_top,
  input[3:0] pp_pkt_byte_cnt_top,
  input[3:0] pp_pkt_type_top
);

  default 
  clocking @(posedge clk);
  endclocking

  default disable iff reset;

	////////////////////////////////////////////////////////////////////////////////	
	// Testing 
	////////////////////////////////////////////////////////////////////////////////	
	logic[3:0] test_var1;
	logic[3:0] test_var2;

  // SECTION Builder - Parser combined work

  cov_pb_pp_task:                       cover property((pb_byte_cnt == 4'h3 && pb0_start_top) ##[1:$] pp_start_top);

	////////////////////////////////////////////////////////////////////////////////
  // Build task constraints
	////////////////////////////////////////////////////////////////////////////////

  asm_addr_in_stability:                assume property($stable(pb_addr_in));
  asm_max_byte_cnt_stability:           assume property($stable(pb_byte_cnt));
  asm_merg_op_stability:                assume property($stable(pb_data_sel));
  asm_crc_en_stability:                 assume property($stable(pb_crc_en));
  asm_ecc_en_stability:                 assume property($stable(pb_ecc_en));
  asm_pkt_type_stability:               assume property($stable(pb_pkt_type));
  asm_ins_ecc_err_stability:            assume property($stable(pb_ins_ecc_err));
  asm_ins_crc_err_stability:            assume property($stable(pb_ins_crc_err));
  asm_ecc_val_stability:                assume property($stable(pb_ecc_val));
  asm_crc_val_stability:                assume property($stable(pb_crc_val));
  asm_sop_val_stability:                assume property($stable(pb_sop_val));
  asm_addr_out_stability:               assume property($stable(pb_addr_out));

  asm_addr_in:                          assume property(pb_addr_in[31:4] == '0);
	asm_inmem_bound:                      assume property(pb_byte_cnt + pb_addr_in <= 18);
	asm_outmem_bound:                     assume property(pb_byte_cnt + pb_addr_out + 3 <= 18);
  asm_addr_out:                         assume property(pb_addr_out[31:4] == '0);
  asm_merging_option:                   assume property(pb_data_sel inside {4'h0, 4'h1, 4'h2});
	////////////////////////////////////////////////////////////////////////////////
  // Parse task constraints
	////////////////////////////////////////////////////////////////////////////////

  asm_addr_hdr_i_stability:             assume property ($stable(pp_addr_hdr));
  asm_ignore_ecc_err_stability:         assume property ($stable(pp_ignore_ecc_err));

  asm_addr_hdr_i:                       assume property (pp_addr_hdr[31:4] == '0);
	////////////////////////////////////////////////////////////////////////////////
  // Top interface cover properties
	////////////////////////////////////////////////////////////////////////////////

  cov_pb0_start:                        cover property(pb0_start_top == 1'b1);
  cov_pb0_end:                          cover property(pb0_irq_top == 1'b1);
  cov_pb0_start_byte_cnt0:              cover property(pb0_start_top == 1'b1 && pb0_byte_cnt_top == 4'h0);
  cov_pb0_start_byte_cnt7:              cover property(pb0_start_top == 1'b1 && pb0_byte_cnt_top == 4'h7);
  cov_pb1_start:                        cover property(pb1_start_top == 1'b1);
  cov_pb1_end:                          cover property(pb1_irq_top == 1'b1);
  cov_pp_start:                         cover property(pp_start_top == 1'b1);
  cov_pp_end:                           cover property(pp_irq_top == 1'b1);
  cov_pp_start_byte_cnt5:               cover property(pp_start_top == 1'b1 && pp_pkt_byte_cnt_top == 4'h5);
  cov_pp_byte_cnt5:                     cover property(pp_pkt_byte_cnt_top == 4'h5);
  cov_ecc_corr_err:                     cover property(pp_pkt_ecc_corr_top == 1'b1);
  cov_no_ecc_corr_err:                  cover property(pp_pkt_ecc_corr_top == 1'b0);
  cov_ecc_uncorr_err:                   cover property(pp_pkt_ecc_uncorr_top == 1'b1);
  cov_no_ecc_uncorr_err:                cover property(pp_pkt_ecc_uncorr_top == 1'b0);
  cov_crc_err:                          cover property(pp_pkt_crc_err_top == 1'b1);
  cov_no_crc_err:                       cover property(pp_pkt_crc_err_top == 1'b0);

	//SECTION Cover points
	cov_pp_pb0_work:                      cover property(!pp_busy_top && !pb0_busy_top);
	cov_pp_pb1_work:                      cover property(!pp_busy_top && !pb1_busy_top);
	cov_pb0_pb1_work:                     cover property(!pb1_busy_top && !pb0_busy_top);
	cov_pb0_pb1_long_work:                cover property((!pb1_busy_top && !pb0_busy_top)[*5]);
	cov_pb0_work:                         cover property(pb0_start_top);
	cov_pb0_check:                        cover property((!pb0_busy_top && pb0_checker_en) ##[1:$] pb0_irq_top);
	cov_pb1_check:                        cover property((!pb1_busy_top && pb1_checker_en) ##[1:$] pb1_irq_top);
	cov_2pb0:                             cover property(pb0_irq_top[->2]);
	cov_2pb1:                             cover property(pb0_irq_top[->2]);
	cov_2pp:                              cover property(pb0_irq_top[->2]);
	////////////////////////////////////////////////////////////////////////////////	
	// LIVENESS props
	////////////////////////////////////////////////////////////////////////////////	
	
	// asm_pb_irq_stable: assume property(pb_irq && !(pb0_start_top || pb1_start_top) |=> pb_irq)
	// asm_pp_irq_stable: assume property(pp_irq && !(pp_start_top) |=> pp_irq)

	// Build task has priority over parse task
	// One cycle latency of ext_irqs in controller because of ex_regs

	// 1. Building has priority
	// 2. No internal int req, because it leads to intr clear state
	// 3. Two builders are available, which makes it impossible (due to controller's long latency) that both of them are busy
	// 	3a. But if IVA is enabled then it must be taken into account

	ast_pb_start_live:                     assert property(pb_irq && (pb0_busy_top && pb1_busy_top)[*2] ##1 !(pp_irq_top || pb0_irq_top || pb1_irq_top) && !cont_busy_top |=> s_eventually (pb0_start_top || pb1_start_top));
	ast_pb0_finish_live:                   assert property(pb0_start_top |=> s_eventually pb0_irq_top);
	ast_pb1_finish_live:                   assert property(pb1_start_top |=> s_eventually pb1_irq_top);

	// 1. Build task req low
	// 2. No internal int req, because it leads to intr clear state
	// 3. Parser must be free, because it leads to task drop
	// 4. In very first cycle block cannot be busy which then triggers property even though on the next cycle blocks start processing because of iva start

	ast_pp_start_live:                     assert property(pp_irq && !pb_irq && pp_busy_top[*2] ##1 !(pp_irq_top || pb0_irq_top || pb1_irq_top) && !cont_busy_top |=> s_eventually pp_start_top);
	ast_pp_finish_live:                    assert property(pp_start_top |=> s_eventually pp_irq_top);

	////////////////////////////////////////////////////////////////////////////////	
	// IMPORTANT Assert valid register values
	////////////////////////////////////////////////////////////////////////////////	

  ast_top_reg_pb0_addr_in:              assert property(pb0_start_top |-> pb0_addr_in_top == pb_addr_in);
  ast_top_reg_pb0_byte_cnt:             assert property(pb0_start_top |-> pb0_byte_cnt_top == pb_byte_cnt);
  ast_top_reg_pb0_pkt_type:             assert property(pb0_start_top |-> pb0_pkt_type_top == pb_pkt_type);
  ast_top_reg_pb0_ecc_en:               assert property(pb0_start_top |-> pb0_ecc_en_top == pb_ecc_en);
  ast_top_reg_pb0_crc_en:               assert property(pb0_start_top |-> pb0_crc_en_top == pb_crc_en);
  ast_top_reg_pb0_ins_ecc_err:          assert property(pb0_start_top |-> pb0_ins_ecc_err_top == pb_ins_ecc_err);
  ast_top_reg_pb0_ins_crc_err:          assert property(pb0_start_top |-> pb0_ins_crc_err_top == pb_ins_crc_err);
  ast_top_reg_pb0_ecc_val:              assert property(pb0_start_top |-> pb0_ecc_val_top == pb_ecc_val);
  ast_top_reg_pb0_crc_val:              assert property(pb0_start_top |-> pb0_crc_val_top == pb_crc_val);
  ast_top_reg_pb0_sop_val:              assert property(pb0_start_top |-> pb0_sop_val_top == pb_sop_val);
  ast_top_reg_pb0_data_sel:             assert property(pb0_start_top |-> pb0_data_sel_top == pb_data_sel);
  ast_top_reg_pb0_addr_out:             assert property(pb0_start_top |-> pb0_addr_out_top == pb_addr_out);

  ast_top_reg_pb1_addr_in:              assert property(pb1_start_top |-> pb1_addr_in_top == pb_addr_in);
  ast_top_reg_pb1_byte_cnt:             assert property(pb1_start_top |-> pb1_byte_cnt_top == pb_byte_cnt);
  ast_top_reg_pb1_pkt_type:             assert property(pb1_start_top |-> pb1_pkt_type_top == pb_pkt_type);
  ast_top_reg_pb1_ecc_en:               assert property(pb1_start_top |-> pb1_ecc_en_top == pb_ecc_en);
  ast_top_reg_pb1_crc_en:               assert property(pb1_start_top |-> pb1_crc_en_top == pb_crc_en);
  ast_top_reg_pb1_ins_ecc_err:          assert property(pb1_start_top |-> pb1_ins_ecc_err_top == pb_ins_ecc_err);
  ast_top_reg_pb1_ins_crc_err:          assert property(pb1_start_top |-> pb1_ins_crc_err_top == pb_ins_crc_err);
  ast_top_reg_pb1_ecc_val:              assert property(pb1_start_top |-> pb1_ecc_val_top == pb_ecc_val);
  ast_top_reg_pb1_crc_val:              assert property(pb1_start_top |-> pb1_crc_val_top == pb_crc_val);
  ast_top_reg_pb1_sop_val:              assert property(pb1_start_top |-> pb1_sop_val_top == pb_sop_val);
  ast_top_reg_pb1_data_sel:             assert property(pb1_start_top |-> pb1_data_sel_top == pb_data_sel);
  ast_top_reg_pb1_addr_out:             assert property(pb1_start_top |-> pb1_addr_out_top == pb_addr_out);

  ast_top_reg_pp_addr_hdr:              assert property(pp_start_top |-> pp_addr_hdr_top == pp_addr_hdr);
  ast_top_reg_pp_ignore_ecc_err:        assert property(pp_start_top |-> pp_ignore_ecc_err_top == pp_ignore_ecc_err);


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
	asm_pp_addr_deadend: assume property(pp_byte_cnt + pp_addr_hdr + 3 <= 14'h12);
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

	// Mid-result crc register block
	always @(posedge clk) begin
		if(reset)
			crc_mid_result_reg <= '0;
		else if(pp_start_top || corr_err_irq_pulse) 
			crc_mid_result_reg <= '0;
		else
			crc_mid_result_reg <= crc_out_s;
	end

	// CRC calc FSM
	typedef enum {IDLE, HEADER_READ, CRC_CALC, COMPARE_CRC} State;

	State state_reg, state_next;

	assign corr_err_irq_pulse = !corr_err_irq_reg2 && corr_err_irq_reg;

	// detect single error irq edge
	always_ff @(posedge clk) begin
	 	if(reset || pp_irq_top) begin
			corr_err_irq_reg <= 1'b0;
			corr_err_irq_reg2 <= 1'b0;
		end
		else begin
			if(pp_pkt_ecc_corr_top)
				corr_err_irq_reg <= 1'b1;

			corr_err_irq_reg2 <= corr_err_irq_reg;
		end
	end


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
		data_in_s <= '0;
		inmem_pp_we_s <= '0;
		state_next <= state_reg;
		addr_next <= addr_reg;
		byte_cnt_next <= byte_cnt_reg;
		crc_cnt_next <= crc_cnt_reg;
		crc_ext_next <= crc_ext_reg;
		crc_calc_next <= crc_calc_reg;
		crc_err_next <= crc_err_reg;

	  ecc_corr_err_pp_next <= ecc_corr_err_pp_reg;
		ecc_uncorr_err_pp_next <= ecc_uncorr_err_pp_reg;

		// single error interrupt, cancel current execution
		// start again and reset everything with correct byte count data
		if(corr_err_irq_pulse) begin

			byte_cnt_next <= pp_pkt_byte_cnt_top;
			addr_next <= pp_addr_hdr_top + 2;
			crc_cnt_next <= '0;
			crc_ext_next <= '0;
			crc_calc_next <= '0;
			crc_err_next <= '0;

			state_next <= CRC_CALC;
		end 
		else begin

			case(state_reg)
				IDLE: begin 
					crc_cnt_next <= '0;
					if(pp_irq_top) begin
						ecc_corr_err_pp_next <= '0;
						ecc_uncorr_err_pp_next <= '0;
					end

					if(pp_start_top && pp_checker_en) begin
						crc_err_next <= '0;
						addr_next <= pp_addr_hdr_top;
						state_next <= HEADER_READ;
					end else
						state_next <= IDLE;
				end
				//
				HEADER_READ: begin
					// calculate correct ecc
					// pkt_type from memory
					ecc_data_in_pp_calc_s[7:4] <= inmem_data_b_o[11:8];
					// byte_cnt from free variable
					ecc_data_in_pp_calc_s[3:0] <= pp_byte_cnt;

					// enable write
					inmem_pp_we_s <= 1'b1;
					// write byte cnt data in inmem, preserve previous data
					// IMPORTANT when we is held, tool can change any other bit as addition to byte cnt change
					// Here correct ecc code must be inserted

					// Msb bytes which represent data following header
					inmem_pp_data_s[31:8] <= inmem_data_b_o[31:16];
					// Sop
					inmem_pp_data_s[15:13] <= inmem_data_b_o[15:13];
					// ECC Msb
					inmem_pp_data_s[12] <= ecc_msb_pp_calc_s;
					// pkt type
					inmem_pp_data_s[11:8] <= inmem_data_b_o[11:8];
					// byte cnt
					inmem_pp_data_s[7:4] <= pp_byte_cnt;
					// ecc code 
					inmem_pp_data_s[3:0] <= ecc_pp_calc_s;

					// store free data in checker
					byte_cnt_next <= pp_byte_cnt;
					// increment address to start reading data
					addr_next <= addr_reg + 2;
					// Check for errors and compare with parser's conclusion
					//BUG byte count info must come from free variable
					ecc_data_in_pp_s[7:4] <= inmem_data_b_o[11:8];
					ecc_data_in_pp_s[3:0] <= pp_byte_cnt;
					ecc_pp_s <= inmem_data_b_o[3:0];

					if(ecc_err_code_pp_s != '0) begin
						// received ecc msb bit
						if(inmem_data_b_o[12:12])
							ecc_corr_err_pp_next <= 1'b1;
						else 
							ecc_uncorr_err_pp_next <= 1'b1;
					end 
					state_next <= CRC_CALC;
				end
				CRC_CALC: begin
					data_in_s <= inmem_data_b_o[7:0];
					crc_cnt_next <= crc_cnt_reg + 1;
					// increment only if staying in current state
					// addr_next <= addr_reg + 1;
					// store CRC
					//BUG Dead-end 
					// if(crc_cnt_reg == byte_cnt_reg)
					if(addr_reg == pp_addr_hdr_top + byte_cnt_reg)
						crc_calc_next <= crc_out_s;

					//if(crc_cnt_reg == byte_cnt_reg + 1) begin
					//BUG Wrong CRC addr, +3 rather than +1
					if(addr_reg == pp_addr_hdr_top + byte_cnt_reg + 3) begin
						crc_ext_next <= inmem_data_b_o[7:0];
						state_next <= COMPARE_CRC;
					end 
					else begin
						addr_next <= addr_reg + 1;
						state_next <= CRC_CALC;
					end
				end
				COMPARE_CRC: begin
					if(crc_ext_reg == crc_calc_reg) begin
						crc_err_next <= 1'b0;
					end else
						crc_err_next <= 1'b1;

					state_next <= IDLE;
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

	// Asssert correct CRC
	ast_pp_crc_err:                        assert property(pp_irq_top && pp_pkt_crc_err_top && !pp_pkt_ecc_uncorr_top && !pp_pkt_ecc_corr_top |-> crc_err_reg);
	ast_pp_crc_no_err:                     assert property(pp_irq_top && !pp_pkt_crc_err_top && !pp_pkt_ecc_uncorr_top && !pp_pkt_ecc_corr_top |-> !crc_err_reg);
	ast_pp_crc_err_when_ecc_err_exists:    assert property(pp_irq_top && pp_pkt_crc_err_top && !pp_pkt_ecc_uncorr_top && pp_pkt_ecc_corr_top |-> crc_err_reg);
	ast_pp_crc_no_err_when_ecc_err_exists: assert property(pp_irq_top && !pp_pkt_crc_err_top && !pp_pkt_ecc_uncorr_top && pp_pkt_ecc_corr_top |-> !crc_err_reg);

	ast_pp_ecc_corr_err:                   assert property(pp_checker_en && pp_pkt_ecc_corr_top |-> ecc_corr_err_pp_reg);
	ast_pp_ecc_uncorr_err:                 assert property(pp_checker_en && pp_pkt_ecc_uncorr_top |-> ecc_uncorr_err_pp_reg);

	////////////////////////////////////////////////////////////////////////////////	
	// IMPORTANT Check data integrity
	////////////////////////////////////////////////////////////////////////////////	

  logic[3:0] chosen_byte; // CHECKER_INPUT chosen_byte

  asm_chosen_byte_stable_top:           assume property($stable(chosen_byte));
  asm_chosen_byte_op0_top:              assume property(disable iff(reset) pb_data_sel == 4'h0 |-> chosen_byte <= pb_byte_cnt && chosen_byte[1:0] == 2'b0);
  asm_chosen_byte_op1_top:              assume property(disable iff(reset) pb_data_sel == 4'h1 |-> chosen_byte <= pb_byte_cnt && chosen_byte[1] == 1'b0);
  asm_chosen_byte_op2_top:              assume property(disable iff(reset) pb_data_sel == 4'h2 |-> chosen_byte <= pb_byte_cnt);

	////////////////////////////////////////////////////////////////////////////////	
	// Checkers enable logic
	////////////////////////////////////////////////////////////////////////////////	
	logic pb0_checker_en;
	logic pb1_checker_en;
	logic pp_checker_en;
	logic[2:0] chk_en;

	assign chk_en = {pb0_checker_en, pb1_checker_en, pp_checker_en};

  asm_pb0_chk_en_stability:             assume property($stable(pb0_checker_en));
  asm_pb1_chk_en_stability:             assume property($stable(pb1_checker_en));
  asm_pp_chk_en_stability:              assume property($stable(pp_checker_en));
	asm_only_one_active_chk:              assume property($onehot(chk_en));

	////////////////////////////////////////////////////////////////////////////////	
	// PB1 CHECKER
	////////////////////////////////////////////////////////////////////////////////	
	logic[13:0] inmem_addr_pb1_di; 
	logic[13:0] inmem_addr_pb1_crc; 
	logic[13:0] outmem_addr_pb1_di_crc; 
	logic[2:0] state_pb1_di; 
	logic di_err_pb1; 
	logic di_crc_err_pb1; 

	checker_di_top pb1_di(
		.clk(clk),
		.reset(reset),

		.checker_en(pb1_checker_en),
		.pb_start(pb1_start_top),
		.pb_irq_top(pb1_irq_top),
		.pb_crc_en(pb_crc_en),
		.pb_crc_val(pb_crc_val),

		.chosen_byte(chosen_byte),
		.pb_addr_in(pb_addr_in),
		.pb_data_sel(pb_data_sel),
		.pb_byte_cnt(pb_byte_cnt),

		.inmem_data_b_o(inmem_data_b_o),
		.pb_addr_out(pb_addr_out),
		.outmem_data_b_o(outmem_data_b_o),

		.inmem_addr_di(inmem_addr_pb1_di),
		.inmem_addr_crc(inmem_addr_pb1_crc),
		.outmem_addr_di_crc(outmem_addr_pb1_di_crc),
		.state_di(state_pb1_di),
		.di_err(di_err_pb1),
		.di_crc_err(di_crc_err_pb1));

	ast_pb1_di:                            assert property(!di_err_pb1);
	ast_crc_pb1_di:                        assert property(!di_crc_err_pb1);
	cov_test: cover property(subsys.packet_builder1.state_reg == 1);
		
	////////////////////////////////////////////////////////////////////////////////	
	// PB0 CHECKER
	////////////////////////////////////////////////////////////////////////////////	
	logic[13:0] inmem_addr_pb0_di; 
	logic[13:0] inmem_addr_pb0_crc; 
	logic[13:0] outmem_addr_pb0_di_crc; 
	logic[2:0] state_pb0_di; 
	logic di_err_pb0; 
	logic di_crc_err_pb0; 

	checker_di_top pb0_di(
		.clk(clk),
		.reset(reset),

		.checker_en(pb0_checker_en),
		.pb_start(pb0_start_top),
		.pb_irq_top(pb0_irq_top),
		.pb_crc_en(pb_crc_en),
		.pb_crc_val(pb_crc_val),
		.chosen_byte(chosen_byte),
		.pb_addr_in(pb_addr_in),
		.pb_data_sel(pb_data_sel),
		.pb_byte_cnt(pb_byte_cnt),

		.inmem_data_b_o(inmem_data_b_o),
		.pb_addr_out(pb_addr_out),
		.outmem_data_b_o(outmem_data_b_o),

		.inmem_addr_di(inmem_addr_pb0_di),
		.inmem_addr_crc(inmem_addr_pb0_crc),
		.outmem_addr_di_crc(outmem_addr_pb0_di_crc),
		.state_di(state_pb0_di),
		.di_err(di_err_pb0),
		.di_crc_err(di_crc_err_pb0));

	ast_pb0_di:                            assert property(!di_err_pb0);
	ast_crc_pb0_di:                        assert property(!di_crc_err_pb0);

	ast_pb0_op2_di:                        assert property(pb_data_sel == 2 |-> !di_err_pb0);


////////////////////////////////////////////////////////////////////////////////
// HELPERS
////////////////////////////////////////////////////////////////////////////////
typedef enum {IDLE_C, PB_STATUS_READ_C, PP_STATUS_READ_C, CTRL_READ_C, CTRL_SETUP_C, START_TASK_C, INC_DROP_CNT_C, INTR_CLEAR_C} cont_state_type;
cont_state_type cont_state;
logic[31:0] cont_ctrl2;

logic ext_intr;
logic pb0_busy;
logic[31:0] base_addr;
logic[31:0] cont_read_addr;
logic pb_task, pp_task;

// base slave addresses
parameter [31:0] REGS_BASE_ADDR = 32'h00100000;
parameter [31:0] EX_REGS_BASE_ADDR = 32'h00200000;
// registers addresses

//axi
logic cont_rd_vld;
parameter [3:0] CONT = 4'b0001;
parameter [3:0] PB0 = 4'b0010;
parameter [3:0] PB1 = 4'b0100;
parameter [3:0] PP = 4'b1000;
logic[3:0] gnt;

parameter [31:0] PB0_STS = 32'h00000004;
parameter [31:0] PB1_STS = 32'h0000001c;
parameter [31:0] PP_STS = 32'h00000034;

parameter [31:0] EXT_PB_CTRL2 = 32'h00000004;
parameter [31:0] EXT_PB_CTRL3 = 32'h00000008;
parameter [31:0] EXT_PB_CTRL4 = 32'h0000000c;

// Level 1, assert conf read
assign cont_state = subsys.main_controller.state_reg;
assign cont_ctrl2 = subsys.main_controller.regs_conf_fifo.fifo_data_s[0];
assign ext_intr = subsys.exreg.ext_pb_ctrl1_s;
assign pb_busy = !subsys.main_controller.axi_read_data_next[0];
assign cont_rd_vld = subsys.main_controller.axi_read_vld_s;
assign base_addr = subsys.main_controller.axi_base_address_next;
assign cont_read_addr = subsys.main_controller.axi_read_address_reg;


assign pb_task = subsys.main_controller.cnt_max_reg == 2 ? 1 : 0;
assign pp_task = subsys.main_controller.cnt_max_reg == 1 ? 1 : 0;
assign gnt = subsys.intcon.gnt;

// Assert ctrl2_read, pb_addr_in conf should be stored in fifo[0] in CTRL_SETUP state 
////////////////////////////////////////////////////////////////////////////////
ast_ctrl2_read_lv1_target: assert property(subsys.main_controller.cnt_max_reg == 2 && cont_state == CTRL_SETUP_C |-> cont_ctrl2 == pb_addr_in);
////////////////////////////////////////////////////////////////////////////////

ast_idle_pbsr_cfsm_help: assert property(subsys.main_controller.int_irq == 0 && subsys.main_controller.ext_irq == 1 && cont_state == IDLE_C |=> cont_state == PB_STATUS_READ_C);
ast_pbsr_cr_cfsm_help: assert property(ext_intr && !pb_busy && cont_rd_vld && cont_state == PB_STATUS_READ_C |=> cont_state == CTRL_READ_C); 
ast_cr_cs_cfsm_help: assert property(subsys.main_controller.axi_read_last_s && cont_state == CTRL_READ_C |=> cont_state == CTRL_SETUP_C); 

ast_pbsr_past_cfsm_help: assert property(cont_state == PB_STATUS_READ_C |-> $past(cont_state) == IDLE_C || $past(cont_state) == PB_STATUS_READ_C);
ast_pbcr_past_cfsm_help: assert property(cont_state == CTRL_READ_C |-> $past(cont_state) == PB_STATUS_READ_C || $past(cont_state) == PP_STATUS_READ_C || $past(cont_state) == CTRL_READ_C);
ast_idle_from_reset_help: assert property(@(posedge clk) disable iff(0) $fell(reset) |-> cont_state == IDLE_C);

cov_idle_from_reset_help: cover property(@(posedge clk) disable iff(0) $fell(reset) ##0 cont_state == IDLE_C ##2 cont_state == IDLE_C);

// Assert base address
ast_idle_base_addr_help: assert property(subsys.main_controller.int_irq == 0 && subsys.main_controller.ext_irq == 1 && cont_state == IDLE_C |-> base_addr == REGS_BASE_ADDR);
ast_pbsr_base_addr_help: assert property(ext_intr && !pb_busy && cont_rd_vld && cont_state == PB_STATUS_READ_C |-> base_addr == EX_REGS_BASE_ADDR); 
ast_cr_base_addr_help: assert property(subsys.main_controller.axi_read_last_s && cont_state == CTRL_READ_C |-> base_addr == REGS_BASE_ADDR); 

// Assert gnt helpers - FALSE ASSUMPTIONS
// ast_pbsr_gnt_help: assert property(cont_state == PB_STATUS_READ_C && subsys.main_controller.M_AXI_ARVALID |=> gnt == CONT);
// ast_pbcr_gnt_help: assert property(cont_state == CTRL_READ_C && subsys.main_controller.M_AXI_ARVALID |=> gnt == CONT);

// Assert base addr reg
ast_pbsr_base_addr_reg_help: assert property(cont_state == PB_STATUS_READ_C && ((subsys.main_controller.M_AXI_ARVALID || subsys.main_controller.M_AXI_RVALID) && !subsys.main_controller.M_AXI_RLAST) |-> base_addr == REGS_BASE_ADDR);
ast_pbcr_base_addr_reg_help: assert property(cont_state == CTRL_READ_C && ((subsys.main_controller.M_AXI_ARVALID || subsys.main_controller.M_AXI_RVALID) && !subsys.main_controller.M_AXI_RLAST) |-> base_addr == EX_REGS_BASE_ADDR);

// Assert read addr
ast_pbsr_cont_read_addr_help: assert property(pb_task && cont_state == PB_STATUS_READ_C && ((subsys.main_controller.M_AXI_ARVALID || subsys.main_controller.M_AXI_RVALID) && !subsys.main_controller.M_AXI_RLAST) |-> 
															cont_read_addr == PB0_STS || cont_read_addr == PB1_STS);

ast_pbcr_cont_read_addr_help: assert property(pb_task && cont_state == CTRL_READ_C && ((subsys.main_controller.M_AXI_ARVALID || subsys.main_controller.M_AXI_RVALID) && !subsys.main_controller.M_AXI_RLAST) |-> 
															cont_read_addr == EXT_PB_CTRL2 || cont_read_addr == EXT_PB_CTRL3 || cont_read_addr == EXT_PB_CTRL4);

// Assert axi data
ast_ctrl2_ex_slave_axi_help: assert property(subsys.main_controller.cnt_max_reg == 2 && subsys.exreg.ex_regs_cont.axi_arlen_cntr == 0 && subsys.exreg.ex_regs_cont.axi_rvalid && cont_state == CTRL_READ_C |-> subsys.exreg.ex_regs_cont.axi_rdata == pb_addr_in);

// Axi transaction Init Flow
// axi read
ast_init_ctrl_read_axi_help:                assert property(cont_state == PB_STATUS_READ_C ##1 cont_state == CTRL_READ_C |-> subsys.main_controller.axi_read_init_reg);
// ast_init_ctrl_read_axi_help:                assert property(cont_state == CTRL_READ_C |-> subsys.main_controller.axi_read_init_reg);

ast_init_read_txn_ff_axi_help:              assert property(subsys.main_controller.master_axi_cont_ctrl.AXI_READ_INIT_I |=> subsys.main_controller.master_axi_cont_ctrl.init_read_txn_ff);
ast_init_read_txn_pulse_axi_help:           assert property(subsys.main_controller.master_axi_cont_ctrl.init_read_txn_ff |-> subsys.main_controller.master_axi_cont_ctrl.init_read_txn_pulse);
ast_start_single_burst_read_axi_help:       assert property(subsys.main_controller.master_axi_cont_ctrl.init_read_txn_pulse |=> subsys.main_controller.master_axi_cont_ctrl.start_single_burst_read);
ast_arvalid_axi_help:                       assert property(subsys.main_controller.master_axi_cont_ctrl.start_single_burst_read |=> subsys.main_controller.master_axi_cont_ctrl.axi_arvalid);

ast_no_ssb_read_axi_help:               		assert property(subsys.main_controller.master_axi_cont_ctrl.AXI_READ_INIT_I |-> !subsys.main_controller.master_axi_cont_ctrl.start_single_burst_read && 
                                                                                                   													!subsys.main_controller.master_axi_cont_ctrl.burst_read_active);

ast_single_init_axi_help: assert property(subsys.main_controller.master_axi_cont_ctrl.AXI_READ_INIT_I |=> !subsys.main_controller.master_axi_cont_ctrl.AXI_READ_INIT_I);
// HOW TO ASSERT ARVALID?
// ast_rtxn_pbsr_axi_help: assert property(cont_state == PB_STATUS_READ_C |-> s_eventually subsys.main_controller.M_AXI_ARVALID);
// ast_rtxn_pbcr_axi_help: assert property(cont_state == CTRL_READ_C |-> s_eventually subsys.main_controller.M_AXI_ARVALID);

// RLAST cannot arrive if before address channnel 
ast_pbsr_no_rvalid_before_hs_axi_help: assert property(cont_state == PB_STATUS_READ_C && !subsys.system_regs.regs_cont.axi_arv_arr_flag |-> !subsys.main_controller.M_AXI_RVALID || !subsys.main_controller.M_AXI_RLAST);
ast_pbcr_no_rvalid_before_hs_axi_help: assert property(cont_state == CTRL_READ_C && !subsys.exreg.ex_regs_cont.axi_arv_arr_flag |-> !subsys.main_controller.M_AXI_RVALID || !subsys.main_controller.M_AXI_RLAST);

// can be moved to axi checker because it does not depend on cont_state
ast_ex_regs_rchannel_flag1_axi_help: assert property(subsys.exreg.ex_regs_cont.axi_arvalid && subsys.exreg.ex_regs_cont.axi_arready |=> subsys.exreg.ex_regs_cont.axi_arv_arr_flag);
ast_ex_regs_rchannel_flag2_axi_help: assert property(subsys.exreg.ex_regs_cont.axi_rlast |-> subsys.exreg.ex_regs_cont.axi_arv_arr_flag);
ast_ex_regs_rchannel_flag3_axi_help: assert property(subsys.exreg.ex_regs_cont.axi_rlast |=> !subsys.exreg.ex_regs_cont.axi_arv_arr_flag);

// ast_arvalid_when_rlast_axi_help: assert property(subsys.main_controller.M_AXI_RLAST |=> $past(subsys.main_controller.M_AXI_ARVALID, 10));
// cov_pbsr_first_cycle: cover property($changed(cont_state) && cont_state == IDLE_C);





///////////////////////////////////////////////////////////////////////////////	
// Memory interface B arbitration logic between DI and CRC checkers
////////////////////////////////////////////////////////////////////////////////	

	logic[13:0] inmem_addr_b_s;
  const logic[2:0] CHOOSE_BYTE = 3'h1;

	// Packet parser has the priority because builder needs access only in his INMEM_READ state,
	// when work between builder and parser can't be in conflict

	// PB0 and PB1 are in conflict while working in parallel due to IVA
	// Solution is to use free variable which will choose which builder will be checked // Conflict occurs only while trying to access inmem and outmem address ports 
	// So free variable will be used as a selection signal in following logic to distinguish which builder's checker 
	// is going to access memory 

	// MEM ADDR selection
	always_comb begin
		if(!pp_busy_top && pp_checker_en)
			inmem_addr_b_s <= addr_reg;
		else if(!pb0_busy_top && pb0_checker_en)
			if(state_pb0_di == CHOOSE_BYTE)
				inmem_addr_b_s <= inmem_addr_pb0_di;
			else
				inmem_addr_b_s <= inmem_addr_pb0_crc;

		else if(!pb1_busy_top && pb1_checker_en)
			if(state_pb1_di == CHOOSE_BYTE)
				inmem_addr_b_s <= inmem_addr_pb1_di;
			else
				inmem_addr_b_s <= inmem_addr_pb1_crc;
		else
			inmem_addr_b_s <= addr_free;
	end

  asm_inmem_en:                          assume property(inmem_en_b_i == 1'b1);
	// disable inmem write when builders are working to secure data integrity between rtl and checkers
	// enable write when parser's checker configurs byte count info
	asm_pp_write_only:                     assume property(!pp_busy_top || !pb0_busy_top || !pb1_busy_top |-> inmem_we_b_i == inmem_pp_we_s);
	asm_pp_write_data:                     assume property(!pp_busy_top |-> inmem_data_b_i == inmem_pp_data_s);
	// assume address value
	asm_inmem_addr:                        assume property(inmem_addr_b_i == inmem_addr_b_s);
	asm_in_addr_bound:                     assume property(addr_free <= 14'h12);

	// assume addr bound for inmem, addr_free has to be less than x"12" 
	asm_out_addr_bound:                    assume property(outmem_addr_b_i <= 14'h12);

	////////////////////////////////////////////////////////////////////////////////
  //SECTION OUTMEM Interface Port B props
	////////////////////////////////////////////////////////////////////////////////

  // outmem port B top interface, memory read only
  asm_outmem_en:                        assume property(outmem_en_b_i == 1'b1);

  asm_outmem_we:                        assume property(outmem_we_b_i == 1'b0);

	asm_pb0_outmem_addr_part1:             assume property(pb0_checker_en && !pb0_busy_top |-> outmem_addr_b_i == outmem_addr_pb0_di_crc);
	asm_pb0_outmem_addr_part2:             assume property((!pb0_busy_top ##1 pb0_busy_top) and pb0_checker_en |-> outmem_addr_b_i == outmem_addr_pb0_di_crc);
	asm_pb1_outmem_addr:                   assume property(pb1_checker_en and (!pb1_busy_top or (!pb1_busy_top ##1 pb1_busy_top)) |-> outmem_addr_b_i == outmem_addr_pb1_di_crc);
endmodule
