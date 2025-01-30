
////////////////////////////////////////////////////////////////////////////////
// PB0 SST HELPERS
////////////////////////////////////////////////////////////////////////////////
typedef enum {IDLE_C, PB_STATUS_READ_C, PP_STATUS_READ_C, CTRL_READ_C, CTRL_SETUP_C, START_TASK_C, INC_DROP_CNT_C, INTR_CLEAR_C} cont_state_type;
typedef enum {IDLE_PB, INMEM_READ_PB, CRC_LOOP_PB, 
                BUILD_FIRST_PULSE_OP0_PB, BUILD_PULSE_OP0_PB, BUILD_LAST_PULSE_OP0_PB, 
                BUILD_FIRST_PULSE_OP1_PB, BUILD_PULSE_OP1_PB, BUILD_LAST_PULSE_OP1_PB, 
                BUILD_FIRST_PULSE_OP2_PB, BUILD_PULSE_OP2_PB, BUILD_LAST_PULSE_OP2_PB, 
                OUTMEM_WRITE_PB, OUTMEM_WRITE_LAST_PB} pb_state_type;

cont_state_type cont_state;
cont_state_type cont_state_next;
pb_state_type pb0_state;
pb_state_type pb1_state;
logic[31:0] cont_ctrl2;

logic ext_intr;
logic pb0_busy;
logic[31:0] base_addr;
logic[31:0] base_addr_reg;
logic[31:0] cont_read_addr;
logic pb_task, pp_task;

// base slave addresses
parameter [31:0] REGS_BASE_ADDR = 32'h00100000;
parameter [31:0] EX_REGS_BASE_ADDR = 32'h00200000;
parameter [31:0] INMEM_BASE_ADDR = 32'h00000000;
parameter [31:0] OUTMEM_BASE_ADDR = 32'h00010000;
// registers addresses
parameter [7:0] PB0_START = 8'h08;

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
assign cont_state_next = subsys.main_controller.state_next;
assign cont_ctrl2 = subsys.main_controller.regs_conf_fifo.fifo_data_s[0];
assign ext_intr = subsys.exreg.ext_pb_ctrl1_s;
assign pb_busy = !subsys.main_controller.axi_read_data_next[0];
assign cont_rd_vld = subsys.main_controller.axi_read_vld_s;
assign base_addr = subsys.main_controller.axi_base_address_next;
assign base_addr_reg = subsys.main_controller.axi_base_address_reg;
assign cont_read_addr = subsys.main_controller.axi_read_address_reg;


assign pb_task = subsys.main_controller.cnt_max_reg == 2 ? 1 : 0;
assign pp_task = subsys.main_controller.cnt_max_reg == 1 ? 1 : 0;
assign gnt = subsys.intcon.gnt;

// lv3
logic [0:3][31:0] pb0_fifo_in;
logic [0:4][31:0] pb0_fifo_out;

logic [0:3][31:0] pb1_fifo_in;
logic [0:4][31:0] pb1_fifo_out;

logic [0:18][7:0] inmem;
logic [0:18][7:0] outmem;

assign pb0_state = subsys.packet_builder0.state_reg;
assign pb0_fifo_in = subsys.packet_builder0.fifo_in.fifo_data_s;
assign pb0_fifo_out = subsys.packet_builder0.fifo_out.fifo_data_s;

assign pb1_state = subsys.packet_builder1.state_reg;
assign pb1_fifo_in = subsys.packet_builder1.fifo_in.fifo_data_s;
assign pb1_fifo_out = subsys.packet_builder1.fifo_out.fifo_data_s;

assign inmem = inmem.inmem_bram.ram_s;
assign outmem = outmem.inmem_bram.ram_s;
cov_test_array: cover property(pb0_fifo_in[0] == 10);

// Assert ctrl2_read, pb_addr_in conf should be stored in fifo[0] in CTRL_SETUP state 
////////////////////////////////////////////////////////////////////////////////
ast_ctrl2_read_lv1_target: assert property(subsys.main_controller.cnt_max_reg == 2 && cont_state == CTRL_SETUP_C |-> cont_ctrl2 == pb_addr_in);
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// Helper impact: LOW
////////////////////////////////////////////////////////////////////////////////
ast_idle_pbsr_cfsm_help_low: assert property(subsys.main_controller.int_irq == 0 && subsys.main_controller.ext_irq == 1 && cont_state == IDLE_C |=> cont_state == PB_STATUS_READ_C);
ast_pbsr_cr_cfsm_help_low: assert property(ext_intr && !pb_busy && cont_rd_vld && cont_state == PB_STATUS_READ_C |=> cont_state == CTRL_READ_C); 
ast_cr_cs_cfsm_help_low: assert property(subsys.main_controller.axi_read_last_s && cont_state == CTRL_READ_C |=> cont_state == CTRL_SETUP_C); 
ast_pbsr_past_cfsm_help_low: assert property(cont_state == PB_STATUS_READ_C |-> $past(cont_state) == IDLE_C || $past(cont_state) == PB_STATUS_READ_C);
ast_pbcr_past_cfsm_help_low: assert property(cont_state == CTRL_READ_C |-> $past(cont_state) == PB_STATUS_READ_C || $past(cont_state) == PP_STATUS_READ_C || $past(cont_state) == CTRL_READ_C);
ast_idle_from_reset_help_low: assert property(@(posedge clk) disable iff(0) $fell(reset) |-> cont_state == IDLE_C);

cov_idle_from_reset_help_low: cover property(@(posedge clk) disable iff(0) $fell(reset) ##0 cont_state == IDLE_C ##2 cont_state == IDLE_C);

// Assert base address
ast_idle_base_addr_help_low: assert property(subsys.main_controller.int_irq == 0 && subsys.main_controller.ext_irq == 1 && cont_state == IDLE_C |-> base_addr == REGS_BASE_ADDR);
ast_pbsr_base_addr_help_low: assert property(ext_intr && !pb_busy && cont_rd_vld && cont_state == PB_STATUS_READ_C |-> base_addr == EX_REGS_BASE_ADDR); 
ast_cr_base_addr_help_low: assert property(subsys.main_controller.axi_read_last_s && cont_state == CTRL_READ_C |-> base_addr == REGS_BASE_ADDR); 
// Assert base addr reg
ast_pbsr_base_addr_reg_help_low: assert property(cont_state == PB_STATUS_READ_C && ((subsys.main_controller.M_AXI_ARVALID || subsys.main_controller.M_AXI_RVALID) && !subsys.main_controller.M_AXI_RLAST) |-> base_addr == REGS_BASE_ADDR);
ast_pbcr_base_addr_reg_help_low: assert property(cont_state == CTRL_READ_C && ((subsys.main_controller.M_AXI_ARVALID || subsys.main_controller.M_AXI_RVALID) && !subsys.main_controller.M_AXI_RLAST) |-> base_addr == EX_REGS_BASE_ADDR);
// Assert read addr
ast_pbsr_cont_read_addr_help_low: assert property(pb_task && cont_state == PB_STATUS_READ_C && ((subsys.main_controller.M_AXI_ARVALID || subsys.main_controller.M_AXI_RVALID) && !subsys.main_controller.M_AXI_RLAST) |-> 
                                                            cont_read_addr == PB0_STS || cont_read_addr == PB1_STS);
ast_pbcr_cont_read_addr_help_low: assert property(pb_task && cont_state == CTRL_READ_C && ((subsys.main_controller.M_AXI_ARVALID || subsys.main_controller.M_AXI_RVALID) && !subsys.main_controller.M_AXI_RLAST) |-> 
                                                            cont_read_addr == EXT_PB_CTRL2 || cont_read_addr == EXT_PB_CTRL3 || cont_read_addr == EXT_PB_CTRL4);

////////////////////////////////////////////////////////////////////////////////
// Helper impact: HIGH
////////////////////////////////////////////////////////////////////////////////
// new props for base addr and read_addr
ast_pbsr_base_addr_lv1_help_high: assert property(cont_state == PB_STATUS_READ_C |-> base_addr_reg == REGS_BASE_ADDR); 
ast_cr_base_addr_lv1_help_high: assert property(cont_state == CTRL_READ_C |-> base_addr_reg == EX_REGS_BASE_ADDR); 
ast_pbsr_cont_read_addr_lv1_help_high: assert property(pb_task && cont_state == PB_STATUS_READ_C |-> cont_read_addr == PB0_STS || cont_read_addr == PB1_STS);
ast_pbcr_cont_read_addr_lv1_help_high: assert property(pb_task && cont_state == CTRL_READ_C |-> cont_read_addr == 4);
////////////////////////////////////////////////////////////////////////////////

// Assert axi data
ast_ctrl2_ex_slave_axi_help_low: assert property(subsys.main_controller.cnt_max_reg == 2 && subsys.exreg.ex_regs_cont.axi_arlen_cntr == 0 && subsys.exreg.ex_regs_cont.axi_rvalid && cont_state == CTRL_READ_C |-> subsys.exreg.ex_regs_cont.axi_rdata == pb_addr_in);

// Helper impact: MEDIUM
// Axi transaction Init Flow
// axi read
ast_init_ctrl_read_axi_help_low:                assert property(cont_state == PB_STATUS_READ_C ##1 cont_state == CTRL_READ_C |-> subsys.main_controller.axi_read_init_reg);
ast_init_read_txn_ff_axi_help_low:              assert property(subsys.main_controller.master_axi_cont_ctrl.AXI_READ_INIT_I |=> subsys.main_controller.master_axi_cont_ctrl.init_read_txn_ff);
ast_init_read_txn_pulse_axi_help_low:           assert property(subsys.main_controller.master_axi_cont_ctrl.init_read_txn_ff |-> subsys.main_controller.master_axi_cont_ctrl.init_read_txn_pulse);
ast_start_single_burst_read_axi_help_low:       assert property(subsys.main_controller.master_axi_cont_ctrl.init_read_txn_pulse |=> subsys.main_controller.master_axi_cont_ctrl.start_single_burst_read);
ast_arvalid_axi_help_low:                       assert property(subsys.main_controller.master_axi_cont_ctrl.start_single_burst_read |=> subsys.main_controller.master_axi_cont_ctrl.axi_arvalid);
ast_no_ssb_read_axi_help_low:               		assert property(subsys.main_controller.master_axi_cont_ctrl.AXI_READ_INIT_I |-> !subsys.main_controller.master_axi_cont_ctrl.start_single_burst_read && !subsys.main_controller.master_axi_cont_ctrl.burst_read_active);
ast_single_read_init_axi_help_low: assert property(subsys.main_controller.master_axi_cont_ctrl.AXI_READ_INIT_I |=> !subsys.main_controller.master_axi_cont_ctrl.AXI_READ_INIT_I);

// HOW TO ASSERT ARVALID?
// ast_rtxn_pbsr_axi_help_low: assert property(cont_state == PB_STATUS_READ_C |-> s_eventually subsys.main_controller.M_AXI_ARVALID);
// ast_rtxn_pbcr_axi_help_low: assert property(cont_state == CTRL_READ_C |-> s_eventually subsys.main_controller.M_AXI_ARVALID);

// RLAST cannot arrive if before address channnel 
ast_pbsr_no_rvalid_before_hs_axi_help_low: assert property(cont_state == PB_STATUS_READ_C && !subsys.system_regs.regs_cont.axi_arv_arr_flag |-> !subsys.main_controller.M_AXI_RVALID || !subsys.main_controller.M_AXI_RLAST);
ast_pbcr_no_rvalid_before_hs_axi_help_low: assert property(cont_state == CTRL_READ_C && !subsys.exreg.ex_regs_cont.axi_arv_arr_flag |-> !subsys.main_controller.M_AXI_RVALID || !subsys.main_controller.M_AXI_RLAST);

// can be moved to axi checker because it does not depend on cont_state
ast_ex_regs_rchannel_flag1_axi_help_low: assert property(subsys.exreg.ex_regs_cont.axi_arvalid && subsys.exreg.ex_regs_cont.axi_arready |=> subsys.exreg.ex_regs_cont.axi_arv_arr_flag);
ast_ex_regs_rchannel_flag2_axi_help_low: assert property(subsys.exreg.ex_regs_cont.axi_rlast |-> subsys.exreg.ex_regs_cont.axi_arv_arr_flag);
ast_ex_regs_rchannel_flag3_axi_help_low: assert property(subsys.exreg.ex_regs_cont.axi_rlast |=> !subsys.exreg.ex_regs_cont.axi_arv_arr_flag);

// ast_arvalid_when_rlast_axi_help_low: assert property(subsys.main_controller.M_AXI_RLAST |=> $past(subsys.main_controller.M_AXI_ARVALID, 10));
// cov_pbsr_first_cycle: cover property($changed(cont_state) && cont_state == IDLE_C);

////////////////////////////////////////////////////////////////////////////////
// Helper impact: LOW
////////////////////////////////////////////////////////////////////////////////

// controller's axi write init flow
ast_init_ctrl_write_axi_help_low:                assert property(cont_state == IDLE_C ##1 cont_state == PB_STATUS_READ_C |-> !subsys.main_controller.axi_write_init_reg);

ast_init_write_txn_ff_axi_help_low:              assert property(subsys.main_controller.master_axi_cont_ctrl.AXI_WRITE_INIT_I |=> subsys.main_controller.master_axi_cont_ctrl.init_write_txn_ff);
ast_init_write_txn_pulse_axi_help_low:           assert property(subsys.main_controller.master_axi_cont_ctrl.init_write_txn_ff |-> subsys.main_controller.master_axi_cont_ctrl.init_write_txn_pulse);
ast_start_single_burst_write_axi_help_low:       assert property(subsys.main_controller.master_axi_cont_ctrl.init_write_txn_pulse |=> subsys.main_controller.master_axi_cont_ctrl.start_single_burst_write);
ast_awvalid_axi_help_low:                       assert property(subsys.main_controller.master_axi_cont_ctrl.start_single_burst_write |=> subsys.main_controller.master_axi_cont_ctrl.axi_awvalid);

ast_no_ssb_write_axi_help_low:               		assert property(subsys.main_controller.master_axi_cont_ctrl.AXI_WRITE_INIT_I |-> !subsys.main_controller.master_axi_cont_ctrl.start_single_burst_write && !subsys.main_controller.master_axi_cont_ctrl.burst_write_active);

ast_single_write_init_axi_help_low: assert property(subsys.main_controller.master_axi_cont_ctrl.AXI_WRITE_INIT_I |=> !subsys.main_controller.master_axi_cont_ctrl.AXI_WRITE_INIT_I);

////////////////////////////////////////////////////////////////////////////////
// Helper impact: MEDIUM
////////////////////////////////////////////////////////////////////////////////
// 9. No write in read states

ast_idle_no_next_write_axi_help_low: assert property(cont_state_next == PB_STATUS_READ_C  |-> !subsys.main_controller.axi_write_init_next);

ast_pbsr_no_write_init_reg_axi_help_low: assert property(cont_state == PB_STATUS_READ_C  |-> !subsys.main_controller.axi_write_init_reg);

ast_pbsr_no_write_init_pulse_axi_help_low: assert property(cont_state == PB_STATUS_READ_C  |-> !subsys.main_controller.master_axi_cont_ctrl.init_write_txn_pulse);
ast_pbsr_no_write_active_axi_help_low: assert property(cont_state == PB_STATUS_READ_C  |-> !subsys.main_controller.master_axi_cont_ctrl.burst_write_active);
ast_pbsr_no_write_init_start_axi_help_low: assert property(cont_state == PB_STATUS_READ_C  |-> !subsys.main_controller.master_axi_cont_ctrl.start_single_burst_write);
ast_pbsr_no_awvalid_axi_lv1_help_high: assert property(cont_state == PB_STATUS_READ_C  |-> !subsys.main_controller.M_AXI_AWVALID);
ast_pbsr_no_next_write_axi_help_low: assert property(cont_state_next == CTRL_READ_C  |-> !subsys.main_controller.axi_write_init_next);

ast_pbcr_no_write_init_reg_axi_help_low: assert property(cont_state == CTRL_READ_C  |-> !subsys.main_controller.axi_write_init_reg);

ast_pbcr_no_write_init_pulse_axi_help_low: assert property(cont_state == CTRL_READ_C  |-> !subsys.main_controller.master_axi_cont_ctrl.init_write_txn_pulse);
ast_pbcr_no_write_active_axi_help_low: assert property(cont_state == CTRL_READ_C  |-> !subsys.main_controller.master_axi_cont_ctrl.burst_write_active);
ast_pbcr_no_write_init_start_axi_help_low: assert property(cont_state == CTRL_READ_C  |-> !subsys.main_controller.master_axi_cont_ctrl.start_single_burst_write);
ast_pbcr_no_awvalid_axi_lv1_help_high: assert property(cont_state == CTRL_READ_C  |-> !subsys.main_controller.M_AXI_AWVALID);

////////////////////////////////////////////////////////////////////////////////
// Helper impact: HIGH -> if asserted, have high impact to many cycles in the past, constraining large amount of invalid states from being analyzed
////////////////////////////////////////////////////////////////////////////////
// 10. handshake props 
ast_pbsr_handshake_axi_help_low: assert property(cont_state == PB_STATUS_READ_C && subsys.main_controller.M_AXI_RLAST |-> subsys.main_controller.M_AXI_RVALID);
ast_pbsr_handshake_stop_axi_lv1_help_high: assert property(cont_state == PB_STATUS_READ_C && subsys.main_controller.M_AXI_RVALID |=> !subsys.main_controller.M_AXI_RVALID);

ast_pbcr_handshake_axi_help_low: assert property(pb_task && cont_state == CTRL_READ_C && subsys.main_controller.M_AXI_RLAST |-> subsys.main_controller.M_AXI_RVALID && $past(subsys.main_controller.M_AXI_RVALID) && $past(subsys.main_controller.M_AXI_RVALID, 2));
ast_pbcr_handshake_stop_axi_lv1_help_high: assert property(pb_task && cont_state == CTRL_READ_C && subsys.main_controller.M_AXI_RVALID[*3] |=> !subsys.main_controller.M_AXI_RVALID);

////////////////////////////////////////////////////////////////////////////////
// Helper impact: HIGH
////////////////////////////////////////////////////////////////////////////////
// 11. Fifo
ast_cont_wptr_fifo_lv1_help_high: assert property(cont_state == CTRL_READ_C && $rose(subsys.main_controller.M_AXI_RVALID) |-> subsys.main_controller.regs_conf_fifo.write_index_s == 0);


////////////////////////////////////////////////////////////////////////////////
// level 2 target
////////////////////////////////////////////////////////////////////////////////
property blocks_base_addr_read(rvalid, address);
    rvalid |-> address[31:8] == INMEM_BASE_ADDR[31:8];
endproperty

property blocks_base_addr_write(wvalid, address);
    wvalid |-> address[31:8] == OUTMEM_BASE_ADDR[31:8];
endproperty

property cont_base_addr_read(rvalid, address);
    rvalid |-> address[31:8] == EX_REGS_BASE_ADDR[31:8] || address[31:8] == REGS_BASE_ADDR[31:8];
endproperty

property cont_base_addr_write(wvalid, address);
    wvalid |-> address[31:8] == EX_REGS_BASE_ADDR[31:8] || address[31:8] == REGS_BASE_ADDR[31:8];
endproperty

// 12. base address of controller, pb0, pb1 and pp
ast_cont_read_base_addr_lv2_help_high: assert property(cont_base_addr_read(subsys.main_controller.M_AXI_RVALID, subsys.main_controller.M_AXI_ARADDR));
ast_cont_write_base_addr_lv2_help_high: assert property(cont_base_addr_read(subsys.main_controller.M_AXI_WVALID, subsys.main_controller.M_AXI_AWADDR));

ast_pb0_read_base_addr_lv2_help_high: assert property(blocks_base_addr_read(subsys.packet_builder0.M_AXI_RVALID, subsys.packet_builder0.M_AXI_ARADDR));
ast_pb0_write_base_addr_lv2_help_high: assert property(blocks_base_addr_write(subsys.packet_builder0.M_AXI_WVALID, subsys.packet_builder0.M_AXI_AWADDR));
ast_pb1_read_base_addr_lv2_help_high: assert property(blocks_base_addr_read(subsys.packet_builder1.M_AXI_RVALID, subsys.packet_builder1.M_AXI_ARADDR));
ast_pb1_write_base_addr_lv2_help_high: assert property(blocks_base_addr_write(subsys.packet_builder1.M_AXI_WVALID, subsys.packet_builder1.M_AXI_AWADDR));

ast_pp_read_base_addr_lv2_help_high: assert property(blocks_base_addr_read(subsys.parser.M_AXI_RVALID, subsys.parser.M_AXI_ARADDR));

ast_pp_no_write_lv2_help_high: assert property(!subsys.parser.M_AXI_WVALID && !subsys.parser.M_AXI_AWVALID);

// 13. start address must be on the bus when start is asserted
ast_cont_addr_st_lv2_help_high: assert property(pb0_start_top |-> subsys.main_controller.M_AXI_AWADDR == (REGS_BASE_ADDR + PB0_START));

// 14. start can be only asserted from START_TASK
ast_cont_state_st_lv2_help_low: assert property(pb0_start_top |-> cont_state  == START_TASK_C);
// 15. 
ast_rise_wvalid_st_lv2_help_low: assert property(pb0_start_top |-> $past(subsys.main_controller.M_AXI_WVALID));
ast_rise_wlast_st_lv2_help_low: assert property(pb0_start_top |-> $past(subsys.main_controller.M_AXI_WLAST));
ast_rise_wready_st_lv2_help_low: assert property(pb0_start_top |-> $past(subsys.main_controller.M_AXI_WREADY));
ast_hs_stop_st_lv2_help_low: assert property(cont_state == START_TASK_C && subsys.main_controller.M_AXI_WREADY |=> !subsys.main_controller.M_AXI_WREADY);
ast_write_done_st_lv2_help_low: assert property(pb0_start_top |-> $rose(subsys.main_controller.axi_write_done_s));

// 16.  not verified
ast_hs_cs_lv2_help_low: assert property(pb_task && cont_state == CTRL_SETUP_C && subsys.main_controller.axi_write_done_s |-> $past(subsys.main_controller.M_AXI_WREADY, 1) &&  $past(subsys.main_controller.M_AXI_WREADY, 2) && $past(subsys.main_controller.M_AXI_WREADY, 3));
ast_hs2_cs_lv2_help_low: assert property(cont_state == CTRL_SETUP_C && subsys.main_controller.axi_write_done_s |-> $past(!subsys.main_controller.M_AXI_WREADY, 4));
ast_hs_stop_cs_lv2_help_low: assert property(cont_state == CTRL_SETUP_C && subsys.main_controller.M_AXI_WREADY[*3] |=> !subsys.main_controller.M_AXI_WREADY);

// 18. connect ctrl_setup with start_task
ast_winit_cs_lv2_help_low: assert property(cont_state == START_TASK_C && subsys.main_controller.axi_write_init_reg |-> $past(cont_state) == CTRL_SETUP_C);

// 19. regs wchannel flag low when write done, eqv write_done and bvalid
ast_regs_wchannel_flag_lv2_help_low: assert property(subsys.main_controller.axi_write_done_s |-> !subsys.system_regs.regs_cont.axi_awv_awr_flag);
ast_eqv_write_done_bvalid_lv2_help_low: assert property(subsys.main_controller.axi_write_done_s == subsys.main_controller.M_AXI_BVALID);

// 20. state change after reset
ast_cont_state_after_start_lv2_help_low: assert property(pb0_start_top |=> $changed(cont_state));

// 21. wready eqv, cont st gnt
ast_eqv_wready_st_lv2_help_low: assert property(subsys.main_controller.M_AXI_AWADDR[31:8] == REGS_BASE_ADDR[31:8] |-> subsys.main_controller.M_AXI_WREADY == subsys.system_regs.S_AXI_WREADY);
ast_gnt_st_lv2_help_low: assert property(subsys.main_controller.M_AXI_WREADY |-> $past(gnt, 2) == CONT);

////////////////////////////////////////////////////////////////////////////////
// Helper impact: MEDIUM-HIGH
////////////////////////////////////////////////////////////////////////////////
// 22. assert pb_task when start
ast_pb_task_lv2_help_high: assert property(pb0_start_top |-> subsys.main_controller.cnt_max_reg == 2 && pb_task);

// 23. write_init_flow
ast_wstart_lv2_help_low: assert property($rose(subsys.main_controller.M_AXI_AWVALID) |-> $past(subsys.main_controller.master_axi_cont_ctrl.start_single_burst_write) && $past(!subsys.main_controller.master_axi_cont_ctrl.start_single_burst_write, 2));
ast_wpulse_lv2_help_low: assert property($rose(subsys.main_controller.master_axi_cont_ctrl.start_single_burst_write) |-> $past(subsys.main_controller.master_axi_cont_ctrl.init_write_txn_pulse) && $past(!subsys.main_controller.master_axi_cont_ctrl.init_write_txn_pulse, 2));
ast_winit_lv2_help_low: assert property($rose(subsys.main_controller.master_axi_cont_ctrl.init_write_txn_pulse) |-> $past(subsys.main_controller.axi_write_init_reg) && $past(!subsys.main_controller.axi_write_init_reg, 2));

ast_cs_lv2_help_low: assert property(cont_state == START_TASK_C && subsys.main_controller.axi_write_init_reg |-> $past(subsys.main_controller.axi_write_done_s));
ast_hs_cs2_lv2_help_low: assert property(pb_task && cont_state == CTRL_SETUP_C && subsys.main_controller.axi_write_done_s |-> $past(subsys.main_controller.M_AXI_WREADY, 3));

// pb0 task

////////////////////////////////////////////////////////////////////////////////
// Helper impact: HIGH
////////////////////////////////////////////////////////////////////////////////
ast_cs_ctrl2_pb0_lv2_help_high: assert property(pb_task && subsys.main_controller.M_AXI_AWADDR[7:0] == 8 && cont_state == START_TASK_C |-> pb0_addr_in_top == pb_addr_in);

////////////////////////////////////////////////////////////////////////////////
// lv 3 target
////////////////////////////////////////////////////////////////////////////////

// ast_b0_lv3_target: assert property(pb0_state == INMEM_READ_PB && subsys.packet_builder0.axi_read_last_s |=> pb0_fifo_in[0][7:0] == inmem[pb_addr_in]);

logic[3:0] pb0_fifo_in_byte_addr;
logic[7:0] pb0_fifo_in_byte_data;

asm_pb0_fifo_in_byte_addr_stability: assume property($stable(pb0_fifo_in_byte_addr));
asm_pb0_fifo_in_byte_addr: assume property(pb0_fifo_in_byte_addr <= pb_byte_cnt);

always_comb begin
    case(pb0_fifo_in_byte_addr[1:0])
        2'b00: begin 
            pb0_fifo_in_byte_data <= pb0_fifo_in[pb0_fifo_in_byte_addr[3:2]][7:0];
        end
        2'b01: begin 
            pb0_fifo_in_byte_data <= pb0_fifo_in[pb0_fifo_in_byte_addr[3:2]][15:8];
        end
        2'b10: begin 
            pb0_fifo_in_byte_data <= pb0_fifo_in[pb0_fifo_in_byte_addr[3:2]][23:16];
        end
        2'b11: begin 
            pb0_fifo_in_byte_data <= pb0_fifo_in[pb0_fifo_in_byte_addr[3:2]][31:24];
        end
    endcase
end

ast_lv3_target: assert property(pb0_state == INMEM_READ_PB && subsys.packet_builder0.axi_read_last_s |=> pb0_fifo_in_byte_data == inmem[pb_addr_in + pb0_fifo_in_byte_addr]);
// ast_lv3_new_target: assert property(pb0_irq_top || pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB |-> pb0_fifo_in_byte_data == inmem[pb_addr_in + pb0_fifo_in_byte_addr]);


// helpers assertion logic from lv1
ast_pb0_wptr_fifo_lv3_help_high: assert property(pb0_state == INMEM_READ_PB && $rose(subsys.packet_builder0.M_AXI_RVALID) |-> subsys.packet_builder0.fifo_in.write_index_s == 0);
ast_imr_handshake_stop1_axi_lv3_help_high: assert property(pb_byte_cnt[3:2] == 0 && pb0_state == INMEM_READ_PB && subsys.packet_builder0.M_AXI_RVALID[*1] |=> !subsys.packet_builder0.M_AXI_RVALID);
ast_imr_handshake_stop2_axi_lv3_help_high: assert property(pb_byte_cnt[3:2] == 1 && pb0_state == INMEM_READ_PB && subsys.packet_builder0.M_AXI_RVALID[*2] |=> !subsys.packet_builder0.M_AXI_RVALID);
ast_imr_handshake_stop3_axi_lv3_help_high: assert property(pb_byte_cnt[3:2] == 2 && pb0_state == INMEM_READ_PB && subsys.packet_builder0.M_AXI_RVALID[*3] |=> !subsys.packet_builder0.M_AXI_RVALID);
ast_imr_handshake_stop4_axi_lv3_help_high: assert property(pb_byte_cnt[3:2] == 3 && pb0_state == INMEM_READ_PB && subsys.packet_builder0.M_AXI_RVALID[*4] |=> !subsys.packet_builder0.M_AXI_RVALID);

ast_imr_no_awvalid_axi_lv3_help_high: assert property(pb0_state == INMEM_READ_PB  |-> !subsys.packet_builder0.M_AXI_AWVALID);

ast_imr_pb0_base_addr_lv3_help_high: assert property(pb0_state == INMEM_READ_PB |-> subsys.packet_builder0.axi_base_address_s == INMEM_BASE_ADDR); 
ast_imr_pb0_read_addr_lv3_help_high: assert property(pb0_state == INMEM_READ_PB |-> subsys.packet_builder0.axi_read_address_s == pb_addr_in);

ast_imr_rvalid_lv3_help_high: assert property(pb0_state == INMEM_READ_PB && subsys.packet_builder0.axi_read_last_s |-> subsys.packet_builder0.M_AXI_RVALID && subsys.packet_builder0.fifo_in_wr_en_s);

// 25.	Based on byte_cnt, assert burst_len, handshake props just like in lv1 and lv2
ast_imr_handshake1_axi_lv3_help_high: assert property(pb_byte_cnt[3:2] == 0 && pb0_state == INMEM_READ_PB && subsys.packet_builder0.M_AXI_RLAST |-> subsys.packet_builder0.M_AXI_RVALID);
ast_imr_handshake2_axi_lv3_help_high: assert property(pb_byte_cnt[3:2] == 1 && pb0_state == INMEM_READ_PB && subsys.packet_builder0.M_AXI_RLAST |-> subsys.packet_builder0.M_AXI_RVALID && $past(subsys.packet_builder0.M_AXI_RVALID));
ast_imr_handshake3_axi_lv3_help_high: assert property(pb_byte_cnt[3:2] == 2 && pb0_state == INMEM_READ_PB && subsys.packet_builder0.M_AXI_RLAST |-> subsys.packet_builder0.M_AXI_RVALID && $past(subsys.packet_builder0.M_AXI_RVALID, 2));
ast_imr_handshake4_axi_lv3_help_high: assert property(pb_byte_cnt[3:2] == 3 && pb0_state == INMEM_READ_PB && subsys.packet_builder0.M_AXI_RLAST |-> subsys.packet_builder0.M_AXI_RVALID && $past(subsys.packet_builder0.M_AXI_RVALID, 3));

cov_imr_read1: cover property(pb0_irq_top && pb_byte_cnt == 3);
cov_imr_read2: cover property(pb0_irq_top && pb_byte_cnt == 7);
cov_imr_read3: cover property(pb0_irq_top && pb_byte_cnt == 11);
cov_imr_read4: cover property(pb0_irq_top && pb_byte_cnt == 15);

// 26. Pb_addr_in must be in slave while rising edge on rvalid, rvalid is low while arvalid
ast_imr_addr_in_lv3_help_high: assert property($rose(inmem.slave_axi_cont_inmem.S_AXI_RVALID) && pb0_state == INMEM_READ_PB |-> inmem.slave_axi_cont_inmem.axi_araddr == pb_addr_in);
ast_imr_ar_rvalid_lv3_help_high: assert property(subsys.packet_builder0.M_AXI_ARVALID |-> !subsys.packet_builder0.M_AXI_RVALID);

// 27. Only parser’s checker can write to inmem, but in valid space during PB’s INMEM_READ phase parser’s check is in IDLE
// ast_pp_check_idle_lv3_help_high: assert property(pb0_state == INMEM_READ_PB && subsys.packet_builder0.axi_read_last_s |-> state_reg == IDLE);


////////////////////////////////////////////////////////////////////////////////
// lv 4 target
////////////////////////////////////////////////////////////////////////////////
cov_op0_packet_arrived0: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 0 && pb_data_sel == 0);
cov_op0_packet_arrived1: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 3 && pb_data_sel == 0);
cov_op0_packet_arrived2: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 7 && pb_data_sel == 0);
cov_op0_packet_arrived3: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 11 && pb_data_sel == 0);
cov_op0_packet_arrived4: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 15 && pb_data_sel == 0);

cov_op1_packet_arrived0: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 0 && pb_data_sel == 1);
cov_op1_packet_arrived1: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 3 && pb_data_sel == 1);
cov_op1_packet_arrived2: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 7 && pb_data_sel == 1);
cov_op1_packet_arrived3: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 11 && pb_data_sel == 1);
cov_op1_packet_arrived4: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 15 && pb_data_sel == 1);

cov_op2_packet_arrived0: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 0 && pb_data_sel == 2);
cov_op2_packet_arrived1: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 3 && pb_data_sel == 2);
cov_op2_packet_arrived2: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 7 && pb_data_sel == 2);
cov_op2_packet_arrived3: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 11 && pb_data_sel == 2);
cov_op2_packet_arrived4: cover property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && pb_byte_cnt == 15 && pb_data_sel == 2);

logic[3:0] wbyte_cnt_op0;
logic[3:0] wbyte_cnt_op1;
logic[4:0] wbyte_cnt_op2;

// assign wbyte_cnt_op0 = subsys.packet_builder0.write_byte_cnt_op0_s;
// assign wbyte_cnt_op1 = subsys.packet_builder0.write_byte_cnt_op1_s;
// assign wbyte_cnt_op2 = subsys.packet_builder0.write_byte_cnt_op2_s;

assign wbyte_cnt_op0 = pb_byte_cnt[3:2] + 3;
assign wbyte_cnt_op1 = (pb_byte_cnt[3:2] * 2) + (pb_byte_cnt[0] || pb_byte_cnt[1]) + 3;
assign wbyte_cnt_op2 = pb_byte_cnt + 3;

ast_pb0_lv4_new_target: assert property(pb0_checker_en && subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived |=> !subsys.packet_builder0.chk_data_integrity.di_err);
ast_pb1_lv4_new_target: assert property(pb1_checker_en && subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived |=> !subsys.packet_builder0.chk_data_integrity.di_err);
ast_pb_lv4_new_target: assert property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived |=> !subsys.packet_builder0.chk_data_integrity.di_err);

cov_sanity1_lv4_new_target: cover property(subsys.packet_builder0.chk_data_integrity.chosen_byte == 4 && subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && 
                                    subsys.packet_builder0.chk_data_integrity.received_byte_data == 10 && pb_data_sel == 1 && pb_byte_cnt == 10);

cov_sanity2_lv4_new_target: cover property(subsys.packet_builder0.chk_data_integrity.chosen_byte == 2 && subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && 
                                    subsys.packet_builder0.chk_data_integrity.received_byte_data == 13 && pb_data_sel == 2 && pb_byte_cnt == 15);

cov_sanity3_lv4_new_target: cover property(subsys.packet_builder0.chk_data_integrity.chosen_byte == 15 && subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && 
                                    subsys.packet_builder0.chk_data_integrity.received_byte_data == 8 && pb_data_sel == 2 && pb_byte_cnt == 15);

cov_sanity4_lv4_new_target: cover property(subsys.packet_builder0.chk_data_integrity.chosen_byte == 8 && subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && 
                                    subsys.packet_builder0.chk_data_integrity.received_byte_data == 2 && pb_data_sel == 0 && pb_byte_cnt == 15);
// TODO Assertion logic from lv3 but for write transaction
// ast_pb0_rptr_fifo_lv4_help_high: assert property(pb0_state == OUTMEM_WRITE_PB && $rose(subsys.packet_builder0.M_AXI_WVALID) |-> subsys.packet_builder0.fifo_out.read_index_s == 0);

// For single burst write transactions, wlast is not a single event
ast_omw_handshake1_axi_op0_lv4_help_high: assert property(pb_data_sel == 0 && wbyte_cnt_op0[3:2] == 0 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && $fell(subsys.packet_builder0.M_AXI_WLAST) |-> $past(subsys.packet_builder0.M_AXI_WREADY));
ast_omw_handshake2_axi_op0_lv4_help_high: assert property(pb_data_sel == 0 && wbyte_cnt_op0[3:2] == 1 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WLAST |-> subsys.packet_builder0.M_AXI_WREADY && $past(subsys.packet_builder0.M_AXI_WREADY));

ast_omw_handshake1_axi_op1_lv4_help_high: assert property(pb_data_sel == 1 && wbyte_cnt_op1[3:2] == 0 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && $fell(subsys.packet_builder0.M_AXI_WLAST) |-> $past(subsys.packet_builder0.M_AXI_WREADY));
ast_omw_handshake2_axi_op1_lv4_help_high: assert property(pb_data_sel == 1 && wbyte_cnt_op1[3:2] == 1 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WLAST |-> subsys.packet_builder0.M_AXI_WREADY && $past(subsys.packet_builder0.M_AXI_WREADY));
ast_omw_handshake3_axi_op1_lv4_help_high: assert property(pb_data_sel == 1 && wbyte_cnt_op1[3:2] == 2 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WLAST |-> subsys.packet_builder0.M_AXI_WREADY && $past(subsys.packet_builder0.M_AXI_WREADY, 2));

ast_omw_handshake1_axi_op2_lv4_help_high: assert property(pb_data_sel == 2 && wbyte_cnt_op2[4:2] == 0 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && $fell(subsys.packet_builder0.M_AXI_WLAST) |-> $past(subsys.packet_builder0.M_AXI_WREADY));
ast_omw_handshake2_axi_op2_lv4_help_high: assert property(pb_data_sel == 2 && wbyte_cnt_op2[4:2] == 1 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WLAST |-> subsys.packet_builder0.M_AXI_WREADY && $past(subsys.packet_builder0.M_AXI_WREADY));
ast_omw_handshake3_axi_op2_lv4_help_high: assert property(pb_data_sel == 2 && wbyte_cnt_op2[4:2] == 2 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WLAST |-> subsys.packet_builder0.M_AXI_WREADY && $past(subsys.packet_builder0.M_AXI_WREADY, 2));
ast_omw_handshake4_axi_op2_lv4_help_high: assert property(pb_data_sel == 2 && wbyte_cnt_op2[4:2] == 3 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WLAST |-> subsys.packet_builder0.M_AXI_WREADY && $past(subsys.packet_builder0.M_AXI_WREADY, 3));
ast_omw_handshake5_axi_op2_lv4_help_high: assert property(pb_data_sel == 2 && wbyte_cnt_op2[4:2] == 4 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WLAST |-> subsys.packet_builder0.M_AXI_WREADY && $past(subsys.packet_builder0.M_AXI_WREADY, 4));

ast_omw_handshake1_stop1_axi_op0_lv4_help_high: assert property(pb_data_sel == 0 && wbyte_cnt_op0[3:2] == 0 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WREADY[*1] |=> !subsys.packet_builder0.M_AXI_WREADY);
ast_omw_handshake2_stop2_axi_op0_lv4_help_high: assert property(pb_data_sel == 0 && wbyte_cnt_op0[3:2] == 1 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WREADY[*2] |=> !subsys.packet_builder0.M_AXI_WREADY);
ast_omw_handshake1_stop1_axi_op1_lv4_help_high: assert property(pb_data_sel == 1 && wbyte_cnt_op1[3:2] == 0 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WREADY[*1] |=> !subsys.packet_builder0.M_AXI_WREADY);
ast_omw_handshake2_stop2_axi_op1_lv4_help_high: assert property(pb_data_sel == 1 && wbyte_cnt_op1[3:2] == 1 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WREADY[*2] |=> !subsys.packet_builder0.M_AXI_WREADY);
ast_omw_handshake2_stop3_axi_op1_lv4_help_high: assert property(pb_data_sel == 1 && wbyte_cnt_op1[3:2] == 2 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WREADY[*3] |=> !subsys.packet_builder0.M_AXI_WREADY);
ast_omw_handshake1_stop1_axi_op2_lv4_help_high: assert property(pb_data_sel == 2 && wbyte_cnt_op2[4:2] == 0 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WREADY[*1] |=> !subsys.packet_builder0.M_AXI_WREADY);
ast_omw_handshake2_stop2_axi_op2_lv4_help_high: assert property(pb_data_sel == 2 && wbyte_cnt_op2[4:2] == 1 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WREADY[*2] |=> !subsys.packet_builder0.M_AXI_WREADY);
ast_omw_handshake2_stop3_axi_op2_lv4_help_high: assert property(pb_data_sel == 2 && wbyte_cnt_op2[4:2] == 2 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WREADY[*3] |=> !subsys.packet_builder0.M_AXI_WREADY);
ast_omw_handshake2_stop4_axi_op2_lv4_help_high: assert property(pb_data_sel == 2 && wbyte_cnt_op2[4:2] == 3 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WREADY[*4] |=> !subsys.packet_builder0.M_AXI_WREADY);
ast_omw_handshake2_stop5_axi_op2_lv4_help_high: assert property(pb_data_sel == 2 && wbyte_cnt_op2[4:2] == 4 && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && subsys.packet_builder0.M_AXI_WREADY[*5] |=> !subsys.packet_builder0.M_AXI_WREADY);

ast_omw_no_awvalid_axi_lv4_help_high: assert property((pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB)  |-> !subsys.packet_builder0.M_AXI_ARVALID);
ast_omw_pb0_base_addr_lv4_help_high: assert property((pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) |-> subsys.packet_builder0.axi_base_address_s == OUTMEM_BASE_ADDR); 
w_pb0_read_addr_lv4_help_high: assert property((pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) |-> subsys.packet_builder0.axi_write_address_s == pb_addr_out);

// 27. When received byte flag is asserted pb must be in outmem write state (or last)
ast_omw_when_pkt_arrives_lv4_help_high: assert property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && subsys.packet_builder1.busy_s |-> pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB);

// TODO In outmem write state based on byte_cnt and data_sel, write_burst and write_byte_cnt must be valid
ast_omw_wbc_op0_lv4_help_high: assert property(pb_data_sel == 0 && pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB |-> subsys.packet_builder0.write_byte_cnt_op0_s == wbyte_cnt_op0);
ast_omw_wbc_op1_lv4_help_high: assert property(pb_data_sel == 1 && pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB |-> subsys.packet_builder0.write_byte_cnt_op1_s == wbyte_cnt_op1);
ast_omw_wbc_op2_lv4_help_high: assert property(pb_data_sel == 2 && pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB |-> subsys.packet_builder0.write_byte_cnt_op2_s == wbyte_cnt_op2);

// 28.	Handshake when packet arrives, wpulse counter is 0 outside of OUTMEM_WRITE
ast_hs_when_pkt_arrives_lv4_help_high: assert property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived && subsys.packet_builder1.busy_s |-> $past(subsys.packet_builder0.M_AXI_WVALID) && $past(subsys.packet_builder0.M_AXI_WREADY));
ast_wpulse_when_pkt_arrives_lv4_help_high: assert property((pb0_state != OUTMEM_WRITE_PB && pb0_state != OUTMEM_WRITE_LAST_PB) && subsys.packet_builder1.busy_s |-> subsys.packet_builder0.chk_data_integrity.wpulse_cnt == 0);

//29.	Upon wready rising edge fifo_out read ptr and wpulse_cnt must be 0. Data sel on top and in registers must be equal
ast_wpulse_lv4_help_high: assert property((pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && $rose(subsys.packet_builder0.M_AXI_WREADY) |-> subsys.packet_builder0.chk_data_integrity.wpulse_cnt == 0);
ast_pb0_rptr1_fifo2_lv4_help_high: assert property((pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && $rose(subsys.packet_builder0.M_AXI_WVALID) |-> subsys.packet_builder0.fifo_out.read_index_s == 0);
ast_pb0_rptr2_fifo2_lv4_help_high: assert property((pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && $rose(subsys.packet_builder0.M_AXI_WREADY) |-> subsys.packet_builder0.fifo_out.read_index_s == 0);
ast_omw_data_sel_lv4_help_high: assert property((pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) |-> pb_data_sel == subsys.packet_builder0.data_sel_i);

// 30. No overlapping OUTMEM_WRITE states from PB0 and PB1. 
// rpulse must me 0 in OUTMEM_WRITE
// when byte arrives chosen flag must be asserted

cov_omw_pb0_pb1: cover property((pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && (pb1_state == OUTMEM_WRITE_PB || pb1_state == OUTMEM_WRITE_LAST_PB));

ast_no_omw_pb0_pb1_lv4_help_high: assert property(!((pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) && (pb1_state == OUTMEM_WRITE_PB || pb1_state == OUTMEM_WRITE_LAST_PB)));
ast_rpulse_cnt_lv4_help_high: assert property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived |-> subsys.packet_builder0.chk_data_integrity.rpulse_cnt == 0);
ast_chosen_flag_lv4_help_high: assert property(subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived |-> subsys.packet_builder0.chk_data_integrity.chosen_byte_flag);

// 31. In OUTMEM_WRITE_LAST are either wlast or bvalid asserted
ast_owml_bvalid_or_wlast_lv4_help_high: assert property(pb0_state == OUTMEM_WRITE_LAST_PB |-> subsys.packet_builder0.M_AXI_WLAST || subsys.packet_builder0.M_AXI_BVALID);

// 32.	Wready can’t be asserted during wvalid
ast_pb0_no_wready_when_awvalid_lv4_help_high: assert property(subsys.packet_builder0.M_AXI_AWVALID |-> !subsys.packet_builder0.M_AXI_WREADY);
// 		awready must be asserted before $rose(wready)
ast_pb0_awready_lv4_help_high: assert property($rose(subsys.packet_builder0.M_AXI_WREADY) |-> $past(subsys.packet_builder0.M_AXI_AWREADY) && $past(!subsys.packet_builder0.M_AXI_AWREADY, 2));

// 33.	Only one handshake in outmem write_last
ast_omvl_single_hs_lv4_help_high: assert property(pb0_state == OUTMEM_WRITE_LAST_PB && subsys.packet_builder0.M_AXI_WVALID |=> !subsys.packet_builder0.M_AXI_WVALID);

logic[3:0] cb_pb0;
logic[7:0] cbd_pb0;
logic cbf_pb0;

logic[3:0] rb_pb0; 
logic[7:0] rbd_pb0;
logic rbf_pb0;

// 34. Packet integrity check decomposition
assign cb_pb0 = subsys.packet_builder0.chk_data_integrity.chosen_byte_top;
assign cbd_pb0 = subsys.packet_builder0.chk_data_integrity.chosen_byte_data;
assign cbf_pb0 = subsys.packet_builder0.chk_data_integrity.chosen_byte_flag;

assign rb_pb0 = subsys.packet_builder0.chk_data_integrity.received_byte;
assign rbd_pb0 = subsys.packet_builder0.chk_data_integrity.received_byte_data;
assign rbf_pb0 = subsys.packet_builder0.chk_data_integrity.chosen_packet_arrived;

// connect top config with unit checker
assign subsys.packet_builder0.chk_data_integrity.chosen_byte_top = chosen_byte;
assign subsys.packet_builder0.chk_data_integrity.data_sel_top = pb_data_sel;

cov_34_test1_lv4_help_high: cover property(cb_pb0 == 1);
cov_34_test1a_lv4_help_high: cover property(cb_pb0 != 0);
cov_34_test2_lv4_help_high: cover property(rbf_pb0);
cov_34_test3_lv4_help_high: cover property(subsys.packet_builder0.chk_data_integrity.chosen_byte == 1);
cover_chosen_byte_top_lv4_help_high: cover property(chosen_byte == 1);

// same for all ops
ast_b0_lv4_help_high: assert property(cb_pb0 == 0 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[0][23:16]);
// same for all op2 and op1
ast_b1_lv4_help_high: assert property(cb_pb0 == 1 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[0][31:24]);
// only op2
ast_b2_lv4_help_high: assert property(cb_pb0 == 2 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[1][7:0]);
ast_b3_lv4_help_high: assert property(cb_pb0 == 3 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[1][15:8]);
// all three
ast_b4_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 4 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[1][23:16]);
ast_b4_op1_lv4_help_high: assert property(pb_data_sel == 1 && cb_pb0 == 4 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[1][7:0]);
ast_b4_op0_lv4_help_high: assert property(pb_data_sel == 0 && cb_pb0 == 4 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[0][31:24]);
// same for all op2 and op1
ast_b5_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 5 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[1][31:24]);
ast_b5_op1_lv4_help_high: assert property(pb_data_sel == 1 && cb_pb0 == 5 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[1][15:8]);
// only op2
ast_b6_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 6 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[2][7:0]);
ast_b7_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 7 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[2][15:8]);
// all three
ast_b8_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 8 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[2][23:16]);
ast_b8_op1_lv4_help_high: assert property(pb_data_sel == 1 && cb_pb0 == 8 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[1][23:16]);
ast_b8_op0_lv4_help_high: assert property(pb_data_sel == 0 && cb_pb0 == 8 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[1][7:0]);
// same for all op2 and op1
ast_b9_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 9 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[2][31:24]);
ast_b9_op1_lv4_help_high: assert property(pb_data_sel == 1 && cb_pb0 == 9 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[1][31:24]);
// only op2
ast_b10_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 10 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[3][7:0]);
ast_b11_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 11 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[3][15:8]);
// all three
ast_b12_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 12 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[3][23:16]);
ast_b12_op1_lv4_help_high: assert property(pb_data_sel == 1 && cb_pb0 == 12 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[2][7:0]);
ast_b12_op0_lv4_help_high: assert property(pb_data_sel == 0 && cb_pb0 == 12 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[1][15:8]);
// same for all op2 and op1
ast_b13_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 13 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[3][31:24]);
ast_b13_op1_lv4_help_high: assert property(pb_data_sel == 1 && cb_pb0 == 13 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[2][15:8]);
// only op2
ast_b14_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 14 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[4][7:0]);
ast_b15_op2_lv4_help_high: assert property(pb_data_sel == 2 && cb_pb0 == 15 && rbf_pb0 |-> cbd_pb0 == pb0_fifo_out[4][15:8]);

////////////////////////////////////////////////////////////////////////////////
// lv 5 target
////////////////////////////////////////////////////////////////////////////////

cov_op0_pb0_irq0: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 0 && pb_data_sel == 0);
cov_op0_pb0_irq1: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 3 && pb_data_sel == 0);
cov_op0_pb0_irq2: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 7 && pb_data_sel == 0);
cov_op0_pb0_irq3: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 11 && pb_data_sel == 0);
cov_op0_pb0_irq4: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 15 && pb_data_sel == 0);

cov_op1_pb0_irq0: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 0 && pb_data_sel == 1);
cov_op1_pb0_irq1: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 3 && pb_data_sel == 1);
cov_op1_pb0_irq2: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 7 && pb_data_sel == 1);
cov_op1_pb0_irq3: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 11 && pb_data_sel == 1);
cov_op1_pb0_irq4: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 15 && pb_data_sel == 1);

cov_op2_pb0_irq0: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 0 && pb_data_sel == 2);
cov_op2_pb0_irq1: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 3 && pb_data_sel == 2);
cov_op2_pb0_irq2: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 7 && pb_data_sel == 2);
cov_op2_pb0_irq3: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 11 && pb_data_sel == 2);
cov_op2_pb0_irq4: cover property(pb0_checker_en && pb0_irq_top && pb_byte_cnt == 15 && pb_data_sel == 2);

cov_crc_op0_pb0_irq0: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 0 && pb_data_sel == 0);
cov_crc_op0_pb0_irq1: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 3 && pb_data_sel == 0);
cov_crc_op0_pb0_irq2: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 7 && pb_data_sel == 0);
cov_crc_op0_pb0_irq3: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 11 && pb_data_sel == 0);
cov_crc_op0_pb0_irq4: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 15 && pb_data_sel == 0);

cov_crc_op1_pb0_irq0: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 0 && pb_data_sel == 1);
cov_crc_op1_pb0_irq1: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 3 && pb_data_sel == 1);
cov_crc_op1_pb0_irq2: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 7 && pb_data_sel == 1);
cov_crc_op1_pb0_irq3: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 11 && pb_data_sel == 1);
cov_crc_op1_pb0_irq4: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 15 && pb_data_sel == 1);

cov_crc_op2_pb0_irq0: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 0 && pb_data_sel == 2);
cov_crc_op2_pb0_irq1: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 3 && pb_data_sel == 2);
cov_crc_op2_pb0_irq2: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 7 && pb_data_sel == 2);
cov_crc_op2_pb0_irq3: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 11 && pb_data_sel == 2);
cov_crc_op2_pb0_irq4: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 15 && pb_data_sel == 2);


typedef enum {IDLE_DI, CHOOSE_BYTE_DI, CRC_CALC_DI, RECEIVE_BYTE_DI, COMPARE_CRC_DI} di_State;

di_State pb0_di_state_reg;

// assign pb0_di_state_reg = pb0_di.di_state_reg;


// 35.	Wlast must fall when pb0_irq
ast_wlast_fall_pb0_irq_lv5_help_high: assert property(pb0_irq_top |-> $fell(subsys.packet_builder0.M_AXI_WLAST));

// 36.	Byte can be chosen only in INMEM_READ state
ast_chose_byte_state_lv5_help_high: assert property(pb0_di.di_state_reg == CHOOSE_BYTE_DI |-> pb0_state == INMEM_READ_PB);
ast_no_crc_calc_lv5_help_high: assert property(!pb_crc_en |-> pb0_di.di_state_reg != CRC_CALC_DI && pb0_state != CRC_LOOP_PB);

// 37.	Bvalid can not be asserted during awvalid 
ast_no_bvalid_when_awvalid_lv5_help_high: assert property(subsys.packet_builder0.M_AXI_AWVALID |-> !subsys.packet_builder0.M_AXI_BVALID);

// 38.	CRC calc in checker can be only during INMEM_READ or CRC_LOOP phase in builder
// 		Receive byte state can start only during INMEM_READ or CRC_LOOP phase in builder
ast_pb0_chk_states_dep1_lv5_help_high: assert property(pb0_di.di_state_reg == CRC_CALC_DI |-> pb0_state == INMEM_READ_PB || pb0_state == CRC_LOOP_PB);
ast_pb0_chk_states_dep2_lv5_help_high: assert property($changed(pb0_di.di_state_reg) && pb0_di.di_state_reg == RECEIVE_BYTE_DI |-> pb0_state == INMEM_READ_PB || pb0_state == CRC_LOOP_PB);
logic[5:0] op1_crc_addr_count; 
logic[5:0] op1_crc_addr_count_temp1; 
logic[5:0] op1_crc_addr_count_temp2; 

assign op1_crc_addr_count_temp1 = pb_byte_cnt[3:2]*2;
assign op1_crc_addr_count_temp2 = op1_crc_addr_count_temp1 + pb_byte_cnt[3:2];

assign op1_crc_addr_count = pb_addr_in + pb_byte_cnt[3:2] + (pb_byte_cnt[0] || pb_byte_cnt[1]) + op1_crc_addr_count_temp2 + 2'h3;

// 39.	Di_crc_addr_reg when pb0_irq should have the value byte_cnt + 1 + pb_addr_in, except in case of op0 and b0
ast_di_crc_addr_op2_lv5_help_high: assert property(pb_crc_en && pb0_di.di_state_reg == RECEIVE_BYTE_DI && pb_data_sel == 2 |-> pb0_di.di_crc_addr_reg == pb_addr_in + pb_byte_cnt + 1);
ast_di_crc_addr_op1_firstb_lv5_help_high: assert property(pb_crc_en && pb0_di.op1_data_cnt_reg && pb0_di.di_state_reg == RECEIVE_BYTE_DI && pb_data_sel == 1 |-> pb0_di.di_crc_addr_reg == pb_addr_in + pb_byte_cnt + 1);
ast_di_crc_addr_op1_secondb_lv5_help_high: assert property(pb_crc_en && !pb0_di.op1_data_cnt_reg && pb0_di.di_state_reg == RECEIVE_BYTE_DI && pb_data_sel == 1 |-> pb0_di.di_crc_addr_reg == op1_crc_addr_count);
ast_di_crc_addr_op0_b0_lv5_help_high: assert property(pb_crc_en && pb0_di.di_state_reg == RECEIVE_BYTE_DI && pb_data_sel == 0 |-> pb0_di.di_crc_addr_reg == pb_addr_in + 4*(pb_byte_cnt[3:2] + 1));
ast_di_crc_addr_disabled_lv5_help_high: assert property(!pb_crc_en && pb0_di.di_state_reg == RECEIVE_BYTE_DI |-> pb0_di.di_crc_addr_reg == pb_addr_in);

// 40. Use data decomposition from lv4 and assert that chosen_byte_data is equal with cbd_pb0
// This way because cbd must be correct chosen_byte_data will also be
//DISABLED, convergence key
ast_cbd1_lv5_help_high: assert property(pb0_checker_en && pb0_irq_top |-> pb0_di.chosen_byte_data == cbd_pb0);
ast_cbd2_lv5_help_high: assert property(pb0_checker_en && (pb0_state != IDLE_PB && pb0_state != INMEM_READ_PB) |-> pb0_di.chosen_byte_data == cbd_pb0);

////////////////////////////////////////////////////////////////////////////////
// LEVEL 5 decomposition
////////////////////////////////////////////////////////////////////////////////

ast_b0_op2_lv5_help_subtarget: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte== 0 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[0][23:16]);
ast_b0_op1_lv5_help_subtarget: assert property(pb0_checker_en && pb_data_sel == 1 && pb0_di.chosen_byte== 0 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[0][23:16]);
ast_b0_op0_lv5_help_subtarget: assert property(pb0_checker_en && pb_data_sel == 0 && pb0_di.chosen_byte== 0 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[0][23:16]);
// same for all op2 and op1
ast_b1_lv5_help_high: assert property(pb0_checker_en && pb0_di.chosen_byte== 1 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[0][31:24]);
// only op2
ast_b2_lv5_help_high: assert property(pb0_checker_en && pb0_di.chosen_byte== 2 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[1][7:0]);
ast_b3_lv5_help_high: assert property(pb0_checker_en && pb0_di.chosen_byte== 3 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[1][15:8]);
// all three
ast_b4_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 4 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[1][23:16]);
ast_b4_op1_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 1 && pb0_di.chosen_byte == 4 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[1][7:0]);
ast_b4_op0_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 0 && pb0_di.chosen_byte == 4 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[0][31:24]);
// same for all op2 and op1
ast_b5_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 5 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[1][31:24]);
ast_b5_op1_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 1 && pb0_di.chosen_byte == 5 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[1][15:8]);
// only op2
ast_b6_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 6 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[2][7:0]);
ast_b7_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 7 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[2][15:8]);
// all three
ast_b8_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 8 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[2][23:16]);
ast_b8_op1_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 1 && pb0_di.chosen_byte == 8 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[1][23:16]);
ast_b8_op0_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 0 && pb0_di.chosen_byte == 8 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[1][7:0]);
// same for all op2 and op1
ast_b9_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 9 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[2][31:24]);
ast_b9_op1_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 1 && pb0_di.chosen_byte == 9 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[1][31:24]);
// only op2
ast_b10_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 10 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[3][7:0]);
ast_b11_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 11 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[3][15:8]);
// all three
ast_b12_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 12 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[3][23:16]);
ast_b12_op1_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 1 && pb0_di.chosen_byte == 12 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[2][7:0]);
ast_b12_op0_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 0 && pb0_di.chosen_byte == 12 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[1][15:8]);
// same for all op2 and op1
ast_b13_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 13 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[3][31:24]);
ast_b13_op1_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 1 && pb0_di.chosen_byte == 13 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[2][15:8]);
// only op2
ast_b14_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 14 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[4][7:0]);
ast_b15_op2_lv5_help_high: assert property(pb0_checker_en && pb_data_sel == 2 && pb0_di.chosen_byte == 15 && pb0_irq_top |-> pb0_di.chosen_byte_data == pb0_fifo_out[4][15:8]);
////////////////////////////////////////////////////////////////////////////////

// 40.1. Assert checker state
ast_di_chk_state_lv5_help_subtarget_help: assert property(pb0_di.di_state_reg == IDLE_DI || 
                                                        pb0_di.di_state_reg == CHOOSE_BYTE_DI ||
                                                        pb0_di.di_state_reg == CRC_CALC_DI ||
                                                        pb0_di.di_state_reg == RECEIVE_BYTE_DI ||
                                                        pb0_di.di_state_reg == COMPARE_CRC_DI);

// 40.2. Assert checker state, when pb in outmem and checker en, chk must be in received byte state
ast_di_chk_state2_lv5_help_subtarget_help: assert property(pb0_checker_en && (pb0_state == OUTMEM_WRITE_PB || pb0_state == OUTMEM_WRITE_LAST_PB) |-> pb0_di.di_state_reg == RECEIVE_BYTE_DI); 
ast_cbaddr_lv5_help_subtarget_help: assert property(pb0_di.di_state_reg == RECEIVE_BYTE_DI |-> pb0_di.chosen_byte_addr_reg == pb_addr_in + chosen_byte);

// 40.3. When builder rises awvalid it can not have grant already
ast_pb_wgnt_lv5_help_subtarget_help: assert property ($rose(subsys.packet_builder0.M_AXI_AWVALID) |-> subsys.intcon.gnt != 2);

// NOT PROVEN
// ast_pb_fifo_in_lv5_help_subtarget_help: assert property(!pb0_busy_top && pb0_state != INMEM_READ_PB |-> pb0_fifo_in_byte_data == inmem[pb_addr_in + pb0_fifo_in_byte_addr]);


// 41. if awvalid then wvalid must be asserted
ast_wvalid_when_awvalid_lv5_help_high: assert property(subsys.packet_builder0.M_AXI_AWVALID |-> subsys.packet_builder0.M_AXI_WVALID);

// 42. Assert regs while processing blocks are active
ast_reg_pb0_addr_in_lv5_help_high_coverage:              assert property(!pb0_busy_top && pb0_checker_en |-> pb0_addr_in_top == pb_addr_in);
ast_reg_pb0_byte_cnt_lv5_help_high_coverage:             assert property(!pb0_busy_top && pb0_checker_en |-> pb0_byte_cnt_top == pb_byte_cnt);
ast_reg_pb0_pkt_type_lv5_help_high_coverage:             assert property(!pb0_busy_top && pb0_checker_en |-> pb0_pkt_type_top == pb_pkt_type);
ast_reg_pb0_ecc_en_lv5_help_high_coverage:               assert property(!pb0_busy_top && pb0_checker_en |-> pb0_ecc_en_top == pb_ecc_en);
ast_reg_pb0_crc_en_lv5_help_high_coverage:               assert property(!pb0_busy_top && pb0_checker_en |-> pb0_crc_en_top == pb_crc_en);
ast_reg_pb0_ins_ecc_err_lv5_help_high_coverage:          assert property(!pb0_busy_top && pb0_checker_en |-> pb0_ins_ecc_err_top == pb_ins_ecc_err);
ast_reg_pb0_ins_crc_err_lv5_help_high_coverage:          assert property(!pb0_busy_top && pb0_checker_en |-> pb0_ins_crc_err_top == pb_ins_crc_err);
ast_reg_pb0_ecc_val_lv5_help_high_coverage:              assert property(!pb0_busy_top && pb0_checker_en |-> pb0_ecc_val_top == pb_ecc_val);
ast_reg_pb0_crc_val_lv5_help_high_coverage:              assert property(!pb0_busy_top && pb0_checker_en |-> pb0_crc_val_top == pb_crc_val);
ast_reg_pb0_sop_val_lv5_help_high_coverage:              assert property(!pb0_busy_top && pb0_checker_en |-> pb0_sop_val_top == pb_sop_val);
ast_reg_pb0_data_sel_lv5_help_high_coverage:             assert property(!pb0_busy_top && pb0_checker_en |-> pb0_data_sel_top == pb_data_sel);
ast_reg_pb0_addr_out_lv5_help_high_coverage:             assert property(!pb0_busy_top && pb0_checker_en |-> pb0_addr_out_top == pb_addr_out);

ast_reg_pb1_addr_in_lv5_help_high_coverage:              assert property(!pb1_busy_top && pb1_checker_en |-> pb1_addr_in_top == pb_addr_in);
ast_reg_pb1_byte_cnt_lv5_help_high_coverage:             assert property(!pb1_busy_top && pb1_checker_en |-> pb1_byte_cnt_top == pb_byte_cnt);
ast_reg_pb1_pkt_type_lv5_help_high_coverage:             assert property(!pb1_busy_top && pb1_checker_en |-> pb1_pkt_type_top == pb_pkt_type);
ast_reg_pb1_ecc_en_lv5_help_high_coverage:               assert property(!pb1_busy_top && pb1_checker_en |-> pb1_ecc_en_top == pb_ecc_en);
ast_reg_pb1_crc_en_lv5_help_high_coverage:               assert property(!pb1_busy_top && pb1_checker_en |-> pb1_crc_en_top == pb_crc_en);
ast_reg_pb1_ins_ecc_err_lv5_help_high_coverage:          assert property(!pb1_busy_top && pb1_checker_en |-> pb1_ins_ecc_err_top == pb_ins_ecc_err);
ast_reg_pb1_ins_crc_err_lv5_help_high_coverage:          assert property(!pb1_busy_top && pb1_checker_en |-> pb1_ins_crc_err_top == pb_ins_crc_err);
ast_reg_pb1_ecc_val_lv5_help_high_coverage:              assert property(!pb1_busy_top && pb1_checker_en |-> pb1_ecc_val_top == pb_ecc_val);
ast_reg_pb1_crc_val_lv5_help_high_coverage:              assert property(!pb1_busy_top && pb1_checker_en |-> pb1_crc_val_top == pb_crc_val);
ast_reg_pb1_sop_val_lv5_help_high_coverage:              assert property(!pb1_busy_top && pb1_checker_en |-> pb1_sop_val_top == pb_sop_val);
ast_reg_pb1_data_sel_lv5_help_high_coverage:             assert property(!pb1_busy_top && pb1_checker_en |-> pb1_data_sel_top == pb_data_sel);
ast_reg_pb1_addr_out_lv5_help_high_coverage:             assert property(!pb1_busy_top && pb1_checker_en |-> pb1_addr_out_top == pb_addr_out);

ast_reg_pp_addr_hdr_lv5_help_high_coverage:              assert property(!pp_busy_top && pp_checker_en |-> pp_addr_hdr_top == pp_addr_hdr);
ast_reg_pp_ignore_ecc_err_lv5_help_high_coverage:        assert property(!pp_busy_top && pp_checker_en |-> pp_ignore_ecc_err_top == pp_ignore_ecc_err);


cov_pb0_irq_final: cover property(pb_crc_en && pb0_checker_en && pb0_irq_top && pb_byte_cnt == 0 && pb_data_sel == 2 && 
                                    cbd_pb0 == 8'h7d && pb_addr_in == 7 && pb_addr_out == 7);