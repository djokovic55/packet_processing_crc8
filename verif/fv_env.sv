`include "pp_env_pkg.sv"
`ifdef ENV_TEST
	import pp_env_pkg::*;
`endif

module  fv_env(
	input clk,
	input reset,
////////////////////////////////////////////////////////////////////////////////
// Build task configuration
////////////////////////////////////////////////////////////////////////////////
	input pb_irq,
	input[31:0] pb_addr_in, // assumed
	input[3:0] pb_byte_cnt,// assumed
	input[3:0] pb_pkt_type,
	input pb_ecc_en,
	input pb_crc_en,
	input pb_ins_ecc_err,
	input pb_ins_crc_err,
	input[3:0] pb_ecc_val,
	input[7:0] pb_crc_val,
	input[2:0] pb_sop_val,
	input[3:0] pb_data_sel,// assumed
	input[31:0] pb_addr_out,// assumed

////////////////////////////////////////////////////////////////////////////////
// Parse task configuration
////////////////////////////////////////////////////////////////////////////////
	input pp_irq,
	input[31:0] pp_addr_hdr,
	input pp_ignore_ecc_err,

////////////////////////////////////////////////////////////////////////////////
// Inmem port B top interface, used for memory configuration
////////////////////////////////////////////////////////////////////////////////
	input inmem_en_b_i,
	input[31:0] inmem_data_b_i,
	input[13:0] inmem_addr_b_i,
	input[3:0] inmem_we_b_i,
	input[31:0] inmem_data_b_o,

////////////////////////////////////////////////////////////////////////////////
// Outmem port B top interface, memory read only
////////////////////////////////////////////////////////////////////////////////
	input outmem_en_b_i,
	input[31:0] outmem_data_b_i,
	input[13:0] outmem_addr_b_i,
	input[3:0] outmem_we_b_i,
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
	// Checkers enable logic
	////////////////////////////////////////////////////////////////////////////////	
	logic[13:0] addr_free;
	logic pb0_checker_en;
	logic pb1_checker_en;
	logic pp_checker_en;
	logic[2:0] chk_en;

	assign chk_en = {pb0_checker_en, pb1_checker_en, pp_checker_en};

	asm_pb0_chk_en_stability:             assume property($stable(pb0_checker_en));
	asm_pb1_chk_en_stability:             assume property($stable(pb1_checker_en));
	asm_pp_chk_en_stability:              assume property($stable(pp_checker_en));
	asm_only_one_active_chk:              assume property($onehot(chk_en));


	// Interfaces
	// Connected to fv_adapter
	mem_port_intf inmem_port();
	mem_port_intf outmem_port();
	pb_conf_port_intf pb_conf_port();
	pp_conf_port_intf pp_conf_port();
	pb_regs_port_intf pb0_regs_port();
	pb_regs_port_intf pb1_regs_port();
	pp_regs_port_intf pp_regs_port();

	// Connected to checkers
	mem_port_intf inmem_port_pb0();
	mem_port_intf inmem_port_pb1();
	mem_port_intf inmem_port_pp();
	mem_port_intf outmem_port_pb0();
	mem_port_intf outmem_port_pb1();
	
	// Axi 
	axi_probe_intf axi_ctrl_probe();
	axi_probe_intf axi_pb0_probe();
	axi_probe_intf axi_pb1_probe();
	axi_probe_intf axi_pp_probe();
	axi_probe_intf axi_inmem_probe();
	axi_probe_intf axi_outmem_probe();
	axi_probe_intf axi_reg_probe();
	axi_probe_intf axi_exreg_probe();

	// Adapter
	fv_adapter fv_adapter(.*);

	////////////////////////////////////////////////////////////////////////////////	
	// Packet parser checker
	////////////////////////////////////////////////////////////////////////////////	
	checker_pp checker_pp (.*);
	// MEM -> Adapter -> inmem_port <--------> inmem_port_pp <- PP_CHECKER
	// Main connection, the rest at the end
	// assign inmem_port_pp.data_o = inmem_port.data_o;

	checker_pb checker_pb0(
		.clk(clk),
		.reset(reset),
		.pb_checker_en(pb0_checker_en),
		.pb_conf_port(pb_conf_port),
		.inmem_port_pb(inmem_port_pb0),
		.outmem_port_pb(outmem_port_pb0),
		.pb_regs_port(pb0_regs_port)
	);

	checker_pb checker_pb1(
		.clk(clk),
		.reset(reset),
		.pb_checker_en(pb1_checker_en),
		.pb_conf_port(pb_conf_port),
		.inmem_port_pb(inmem_port_pb1),
		.outmem_port_pb(outmem_port_pb1),
		.pb_regs_port(pb1_regs_port)
	);


	// AXI checkers
	checker_axi checker_axi_ctrl(.clk(clk), .reset(reset), .axi_probe(axi_ctrl_probe));
	checker_axi checker_axi_pb0(.clk(clk), .reset(reset), .axi_probe(axi_pb0_probe));
	checker_axi checker_axi_pb1(.clk(clk), .reset(reset), .axi_probe(axi_pb1_probe));
	checker_axi checker_axi_pp(.clk(clk), .reset(reset), .axi_probe(axi_pp_probe));
	checker_axi checker_axi_inmem(.clk(clk), .reset(reset), .axi_probe(axi_inmem_probe));
	checker_axi checker_axi_outmem(.clk(clk), .reset(reset), .axi_probe(axi_outmem_probe));
	checker_axi checker_axi_reg(.clk(clk), .reset(reset), .axi_probe(axi_reg_probe));
	checker_axi checker_axi_exreg(.clk(clk), .reset(reset), .axi_probe(axi_exreg_probe));


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

	// SECTION Builder - Parser combined work
	cov_pb_pp_task:                       cover property((pb_byte_cnt == 4'h3 && pb0_start_top) ##[1:$] pp_start_top);
	////////////////////////////////////////////////////////////////////////////////	
	// LIVENESS props -> MOVE TO CHECHERS
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
	// IMPORTANT Assert valid register values -> MOVE TO CHECKERS
	////////////////////////////////////////////////////////////////////////////////	

	ast_top_reg_pb0_addr_in_lv4_help_high:              assert property(pb0_start_top |-> pb0_addr_in_top == pb_addr_in);
	ast_top_reg_pb0_byte_cnt_lv4_help_high:             assert property(pb0_start_top |-> pb0_byte_cnt_top == pb_byte_cnt);
	ast_top_reg_pb0_pkt_type_lv4_help_high:             assert property(pb0_start_top |-> pb0_pkt_type_top == pb_pkt_type);
	ast_top_reg_pb0_ecc_en_lv4_help_high:               assert property(pb0_start_top |-> pb0_ecc_en_top == pb_ecc_en);
	ast_top_reg_pb0_crc_en_lv4_help_high:               assert property(pb0_start_top |-> pb0_crc_en_top == pb_crc_en);
	ast_top_reg_pb0_ins_ecc_err_lv4_help_high:          assert property(pb0_start_top |-> pb0_ins_ecc_err_top == pb_ins_ecc_err);
	ast_top_reg_pb0_ins_crc_err_lv4_help_high:          assert property(pb0_start_top |-> pb0_ins_crc_err_top == pb_ins_crc_err);
	ast_top_reg_pb0_ecc_val_lv4_help_high:              assert property(pb0_start_top |-> pb0_ecc_val_top == pb_ecc_val);
	ast_top_reg_pb0_crc_val_lv4_help_high:              assert property(pb0_start_top |-> pb0_crc_val_top == pb_crc_val);
	ast_top_reg_pb0_sop_val_lv4_help_high:              assert property(pb0_start_top |-> pb0_sop_val_top == pb_sop_val);
	ast_top_reg_pb0_data_sel_lv4_help_high:             assert property(pb0_start_top |-> pb0_data_sel_top == pb_data_sel);
	ast_top_reg_pb0_addr_out_lv4_help_high:             assert property(pb0_start_top |-> pb0_addr_out_top == pb_addr_out);

	ast_top_reg_pb1_addr_in_lv4_help_high:              assert property(pb1_start_top |-> pb1_addr_in_top == pb_addr_in);
	ast_top_reg_pb1_byte_cnt_lv4_help_high:             assert property(pb1_start_top |-> pb1_byte_cnt_top == pb_byte_cnt);
	ast_top_reg_pb1_pkt_type_lv4_help_high:             assert property(pb1_start_top |-> pb1_pkt_type_top == pb_pkt_type);
	ast_top_reg_pb1_ecc_en_lv4_help_high:               assert property(pb1_start_top |-> pb1_ecc_en_top == pb_ecc_en);
	ast_top_reg_pb1_crc_en_lv4_help_high:               assert property(pb1_start_top |-> pb1_crc_en_top == pb_crc_en);
	ast_top_reg_pb1_ins_ecc_err_lv4_help_high:          assert property(pb1_start_top |-> pb1_ins_ecc_err_top == pb_ins_ecc_err);
	ast_top_reg_pb1_ins_crc_err_lv4_help_high:          assert property(pb1_start_top |-> pb1_ins_crc_err_top == pb_ins_crc_err);
	ast_top_reg_pb1_ecc_val_lv4_help_high:              assert property(pb1_start_top |-> pb1_ecc_val_top == pb_ecc_val);
	ast_top_reg_pb1_crc_val_lv4_help_high:              assert property(pb1_start_top |-> pb1_crc_val_top == pb_crc_val);
	ast_top_reg_pb1_sop_val_lv4_help_high:              assert property(pb1_start_top |-> pb1_sop_val_top == pb_sop_val);
	ast_top_reg_pb1_data_sel_lv4_help_high:             assert property(pb1_start_top |-> pb1_data_sel_top == pb_data_sel);
	ast_top_reg_pb1_addr_out_lv4_help_high:             assert property(pb1_start_top |-> pb1_addr_out_top == pb_addr_out);

	ast_top_reg_pp_addr_hdr_lv4_help_high:              assert property(pp_start_top |-> pp_addr_hdr_top == pp_addr_hdr);
	ast_top_reg_pp_ignore_ecc_err_lv4_help_high:        assert property(pp_start_top |-> pp_ignore_ecc_err_top == pp_ignore_ecc_err);



	`ifdef SST
		`include "sst/pb0_sst_helpers.sv"
	`endif

	///////////////////////////////////////////////////////////////////////////////	
	// INMEM interface B arbitration logic between DI and CRC checkers
	////////////////////////////////////////////////////////////////////////////////	

	logic[13:0] inmem_addr_s;
	const logic[2:0] CHOOSE_BYTE = 3'h1;

	// Packet parser has the priority because builder needs access only in his INMEM_READ state,
	// when work between builder and parser can't be in conflict

	// PB0 and PB1 are in conflict while working in parallel due to IVA
	// Solution is to use free variable which will choose which builder will be checked 
	// Conflict occurs only while trying to access inmem and outmem address ports 
	// So free variable will be used as a selection signal in following logic to distinguish which builder's checker is going to access memory 

	// To simplify the di assertion it is important to register chosen data in receive byte state also
	// This way tool does not have to remember data for many previous cycles
	// When irq arrives read data from inmem and outmem, compare them and conlude wheather there is an error or not

	// Every CEX provided by SST analysis relies on the case when data was never chosen because the inital checker state was RECEIVED_BYTE
	// This way CHOOSE_BYTE phase never occured 

	// MEM ADDR selection
	// All checkers read from INMEM, arbitration required
	always_comb begin
		if(!pp_busy_top && pp_checker_en)
			inmem_addr_s <= inmem_port_pp.addr;
		else if(!pb0_busy_top && pb0_checker_en)
			inmem_addr_s <= inmem_port_pb0.addr;
		else if(!pb1_busy_top && pb1_checker_en)
			inmem_addr_s <= inmem_port_pb1.addr;
		else
			inmem_addr_s <= addr_free;
	end

	// en; // we; // addr; // data_i; // data_o;

	asm_inmem_en:                          assume property(inmem_port.en == 1'b1);
	// disable inmem write when builders are working to secure data integrity between rtl and checkers
	// enable write when parser's checker configurs byte count info
	// ONLY CHECKER_PP can write to INMEM
	asm_inmem_we:                          assume property(!pp_busy_top || !pb0_busy_top || !pb1_busy_top |-> inmem_port.we == inmem_port_pp.we);
	// assume address value
	asm_inmem_addr:                        assume property(inmem_port.addr == inmem_addr_s);
	// assume addr bound for inmem, addr_free has to be less than x"12" 
	asm_in_addr_bound:                     assume property(addr_free <= 14'h12);
	asm_inmem_data_i:                      assume property(!pp_busy_top |-> inmem_port.data_i == inmem_port_pp.data_i);

	// All checkers can read INMEM 
	assign inmem_port_pp.data_o = inmem_port.data_o;
	assign inmem_port_pb0.data_o = inmem_port.data_o;
	assign inmem_port_pb1.data_o = inmem_port.data_o;
	////////////////////////////////////////////////////////////////////////////////
	//SECTION OUTMEM Interface Port B props
	////////////////////////////////////////////////////////////////////////////////
	// outmem port B top interface, memory read only
	asm_outmem_en:                        assume property(outmem_port.en == 1'b1);
	// None can write to OUTMEM
	asm_outmem_we:                        assume property(outmem_port.we == 4'b0000);
	// PB checkers read from OUTMEM, arbitration required
	asm_pb0_outmem_addr_part1:             assume property(pb0_checker_en && !pb0_busy_top |-> outmem_port.addr == outmem_port_pb0.addr);
	asm_pb0_outmem_addr_part2:             assume property((!pb0_busy_top ##1 pb0_busy_top) and pb0_checker_en |-> outmem_port.addr == outmem_port_pb0.addr);
	asm_pb1_outmem_addr:                   assume property(pb1_checker_en and (!pb1_busy_top or (!pb1_busy_top ##1 pb1_busy_top)) |-> outmem_port.addr == outmem_port_pb1.addr);
	asm_out_addr_bound:                    assume property(outmem_addr_b_i <= 14'h12);
	assign outmem_port_pb0.data_o = outmem_port.data_o;
	assign outmem_port_pb1.data_o = outmem_port.data_o;



endmodule
