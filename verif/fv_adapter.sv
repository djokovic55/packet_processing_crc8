
`include "pp_env_pkg.sv"
`include "interfaces/pp_conf_port_intf.sv"
`include "interfaces/pb_conf_port_intf.sv"
`include "interfaces/mem_port_intf.sv"
`include "interfaces/regs_port_intf.sv"
`include "interfaces/axi_probe_intf.sv"
module fv_adapter (
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
	input[3:0] pp_pkt_type_top,

    pb_conf_port_intf.driver pb_conf_port,
    pp_conf_port_intf.driver pp_conf_port,
    mem_port_intf.driver inmem_port,
    mem_port_intf.driver outmem_port,
	pb_regs_port_intf.driver pb0_regs_port,
	pb_regs_port_intf.driver pb1_regs_port,
	pp_regs_port_intf.driver pp_regs_port,

	axi_probe_intf.driver axi_ctrl_probe,
	axi_probe_intf.driver axi_pb0_probe,
	axi_probe_intf.driver axi_pb1_probe,
	axi_probe_intf.driver axi_pp_probe,
	axi_probe_intf.driver axi_inmem_probe,
	axi_probe_intf.driver axi_outmem_probe,
	axi_probe_intf.driver axi_reg_probe,
	axi_probe_intf.driver axi_exreg_probe

);


    assign pb_conf_port.pb_irq = pb_irq;
    assign pb_conf_port.pb_addr_in = pb_addr_in;
    assign pb_conf_port.pb_byte_cnt = pb_byte_cnt;
    assign pb_conf_port.pb_pkt_type = pb_pkt_type;
    assign pb_conf_port.pb_ecc_en = pb_ecc_en;
    assign pb_conf_port.pb_crc_en = pb_crc_en;
    assign pb_conf_port.pb_ins_ecc_err = pb_ins_ecc_err;
    assign pb_conf_port.pb_ins_crc_err = pb_ins_crc_err;
    assign pb_conf_port.pb_ecc_val = pb_ecc_val;
    assign pb_conf_port.pb_crc_val = pb_crc_val;
    assign pb_conf_port.pb_sop_val = pb_sop_val;
    assign pb_conf_port.pb_data_sel = pb_data_sel;
    assign pb_conf_port.pb_addr_out = pb_addr_out;

    assign pp_conf_port.pp_irq = pp_irq;
    assign pp_conf_port.pp_addr_hdr = pp_addr_hdr;
    assign pp_conf_port.pp_ignore_ecc_err = pp_ignore_ecc_err;

    assign inmem_port.en = inmem_en_b_i;
    assign inmem_port.data_i = inmem_data_b_i;
    assign inmem_port.addr = inmem_addr_b_i;
    assign inmem_port.we = inmem_we_b_i;
    assign inmem_port.data_o = inmem_data_b_o;

    assign outmem_port.en = outmem_en_b_i;
    assign outmem_port.data_i = outmem_data_b_i;
    assign outmem_port.addr = outmem_addr_b_i;
    assign outmem_port.we = outmem_we_b_i;
    assign outmem_port.data_o = outmem_data_b_o;

    assign pb0_regs_port.pb_start = pb0_start_top;
    assign pb0_regs_port.pb_busy = pb0_busy_top;
    assign pb0_regs_port.pb_irq = pb0_irq_top;
    assign pb0_regs_port.pb_addr_in = pb0_addr_in_top;
    assign pb0_regs_port.pb_byte_cnt = pb0_byte_cnt_top;
    assign pb0_regs_port.pb_pkt_type = pb0_pkt_type_top;
    assign pb0_regs_port.pb_ecc_en = pb0_ecc_en_top;
    assign pb0_regs_port.pb_crc_en = pb0_crc_en_top;
    assign pb0_regs_port.pb_ins_ecc_err = pb0_ins_ecc_err_top;
    assign pb0_regs_port.pb_ins_crc_err = pb0_ins_crc_err_top;
    assign pb0_regs_port.pb_ecc_val = pb0_ecc_val_top;
    assign pb0_regs_port.pb_crc_val = pb0_crc_val_top;
    assign pb0_regs_port.pb_sop_val = pb0_sop_val_top;
    assign pb0_regs_port.pb_data_sel = pb0_data_sel_top;
    assign pb0_regs_port.pb_addr_out = pb0_addr_out_top;

    assign pb1_regs_port.pb_start = pb1_start_top;
    assign pb1_regs_port.pb_busy = pb1_busy_top;
    assign pb1_regs_port.pb_irq = pb1_irq_top;
    assign pb1_regs_port.pb_addr_in = pb1_addr_in_top;
    assign pb1_regs_port.pb_byte_cnt = pb1_byte_cnt_top;
    assign pb1_regs_port.pb_pkt_type = pb1_pkt_type_top;
    assign pb1_regs_port.pb_ecc_en = pb1_ecc_en_top;
    assign pb1_regs_port.pb_crc_en = pb1_crc_en_top;
    assign pb1_regs_port.pb_ins_ecc_err = pb1_ins_ecc_err_top;
    assign pb1_regs_port.pb_ins_crc_err = pb1_ins_crc_err_top;
    assign pb1_regs_port.pb_ecc_val = pb1_ecc_val_top;
    assign pb1_regs_port.pb_crc_val = pb1_crc_val_top;
    assign pb1_regs_port.pb_sop_val = pb1_sop_val_top;
    assign pb1_regs_port.pb_data_sel = pb1_data_sel_top;
    assign pb1_regs_port.pb_addr_out = pb1_addr_out_top;

    assign pp_regs_port.pp_start = pp_start_top;
    assign pp_regs_port.pp_busy = pp_busy_top;
    assign pp_regs_port.pp_irq = pp_irq_top;
    assign pp_regs_port.pp_addr_hdr = pp_addr_hdr_top;
    assign pp_regs_port.pp_ignore_ecc_err = pp_ignore_ecc_err_top;
    assign pp_regs_port.pp_pkt_ecc_corr = pp_pkt_ecc_corr_top;
    assign pp_regs_port.pp_pkt_ecc_uncorr = pp_pkt_ecc_uncorr_top;
    assign pp_regs_port.pp_pkt_crc_err = pp_pkt_crc_err_top;
    assign pp_regs_port.pp_pkt_byte_cnt = pp_pkt_byte_cnt_top;
    assign pp_regs_port.pp_pkt_type = pp_pkt_type_top;

	// CTRL AXI PROBE
	assign axi_ctrl_probe.awaddr = subsys.intcon.s_axi_int_awaddr_ctrl;
	assign axi_ctrl_probe.awlen = subsys.intcon.s_axi_int_awlen_ctrl;
	assign axi_ctrl_probe.awsize = subsys.intcon.s_axi_int_awsize_ctrl;
	assign axi_ctrl_probe.awburst = subsys.intcon.s_axi_int_awburst_ctrl;
	assign axi_ctrl_probe.awvalid = subsys.intcon.s_axi_int_awvalid_ctrl;
	assign axi_ctrl_probe.awready = subsys.intcon.s_axi_int_awready_ctrl;
	assign axi_ctrl_probe.wdata = subsys.intcon.s_axi_int_wdata_ctrl;
	assign axi_ctrl_probe.wstrb = subsys.intcon.s_axi_int_wstrb_ctrl;
	assign axi_ctrl_probe.wlast = subsys.intcon.s_axi_int_wlast_ctrl;
	assign axi_ctrl_probe.wvalid = subsys.intcon.s_axi_int_wvalid_ctrl;
	assign axi_ctrl_probe.wready = subsys.intcon.s_axi_int_wready_ctrl;
	assign axi_ctrl_probe.bresp = subsys.intcon.s_axi_int_bresp_ctrl;
	assign axi_ctrl_probe.bvalid = subsys.intcon.s_axi_int_bvalid_ctrl;
	assign axi_ctrl_probe.bready = subsys.intcon.s_axi_int_bready_ctrl;
	assign axi_ctrl_probe.araddr = subsys.intcon.s_axi_int_araddr_ctrl;
	assign axi_ctrl_probe.arlen = subsys.intcon.s_axi_int_arlen_ctrl;
	assign axi_ctrl_probe.arsize = subsys.intcon.s_axi_int_arsize_ctrl;
	assign axi_ctrl_probe.arburst = subsys.intcon.s_axi_int_arburst_ctrl;
	assign axi_ctrl_probe.arvalid = subsys.intcon.s_axi_int_arvalid_ctrl;
	assign axi_ctrl_probe.arready = subsys.intcon.s_axi_int_arready_ctrl;
	assign axi_ctrl_probe.rdata = subsys.intcon.s_axi_int_rdata_ctrl;
	assign axi_ctrl_probe.rresp = subsys.intcon.s_axi_int_rresp_ctrl;
	assign axi_ctrl_probe.rlast = subsys.intcon.s_axi_int_rlast_ctrl;
	assign axi_ctrl_probe.rvalid = subsys.intcon.s_axi_int_rvalid_ctrl;
	assign axi_ctrl_probe.rready = subsys.intcon.s_axi_int_rready_ctrl;

	assign axi_pb0_probe.awaddr = subsys.intcon.s_axi_int_awaddr_pb0;
	assign axi_pb0_probe.awlen = subsys.intcon.s_axi_int_awlen_pb0;
	assign axi_pb0_probe.awsize = subsys.intcon.s_axi_int_awsize_pb0;
	assign axi_pb0_probe.awburst = subsys.intcon.s_axi_int_awburst_pb0;
	assign axi_pb0_probe.awvalid = subsys.intcon.s_axi_int_awvalid_pb0;
	assign axi_pb0_probe.awready = subsys.intcon.s_axi_int_awready_pb0;
	assign axi_pb0_probe.wstrb = subsys.intcon.s_axi_int_wstrb_pb0;
	assign axi_pb0_probe.wlast = subsys.intcon.s_axi_int_wlast_pb0;
	assign axi_pb0_probe.wvalid = subsys.intcon.s_axi_int_wvalid_pb0;
	assign axi_pb0_probe.wready = subsys.intcon.s_axi_int_wready_pb0;
	assign axi_pb0_probe.bresp = subsys.intcon.s_axi_int_bresp_pb0;
	assign axi_pb0_probe.bvalid = subsys.intcon.s_axi_int_bvalid_pb0;
	assign axi_pb0_probe.bready = subsys.intcon.s_axi_int_bready_pb0;
	assign axi_pb0_probe.araddr = subsys.intcon.s_axi_int_araddr_pb0;
	assign axi_pb0_probe.arlen = subsys.intcon.s_axi_int_arlen_pb0;
	assign axi_pb0_probe.arsize = subsys.intcon.s_axi_int_arsize_pb0;
	assign axi_pb0_probe.arburst = subsys.intcon.s_axi_int_arburst_pb0;
	assign axi_pb0_probe.arvalid = subsys.intcon.s_axi_int_arvalid_pb0;
	assign axi_pb0_probe.arready = subsys.intcon.s_axi_int_arready_pb0;
	assign axi_pb0_probe.rdata = subsys.intcon.s_axi_int_rdata_pb0;
	assign axi_pb0_probe.rresp = subsys.intcon.s_axi_int_rresp_pb0;
	assign axi_pb0_probe.rlast = subsys.intcon.s_axi_int_rlast_pb0;
	assign axi_pb0_probe.rvalid = subsys.intcon.s_axi_int_rvalid_pb0;
	assign axi_pb0_probe.rready = subsys.intcon.s_axi_int_rready_pb0;

	assign axi_pb1_probe.awaddr = subsys.intcon.s_axi_int_awaddr_pb1;
	assign axi_pb1_probe.awlen = subsys.intcon.s_axi_int_awlen_pb1;
	assign axi_pb1_probe.awsize = subsys.intcon.s_axi_int_awsize_pb1;
	assign axi_pb1_probe.awburst = subsys.intcon.s_axi_int_awburst_pb1;
	assign axi_pb1_probe.awvalid = subsys.intcon.s_axi_int_awvalid_pb1;
	assign axi_pb1_probe.awready = subsys.intcon.s_axi_int_awready_pb1;
	assign axi_pb1_probe.wstrb = subsys.intcon.s_axi_int_wstrb_pb1;
	assign axi_pb1_probe.wlast = subsys.intcon.s_axi_int_wlast_pb1;
	assign axi_pb1_probe.wvalid = subsys.intcon.s_axi_int_wvalid_pb1;
	assign axi_pb1_probe.wready = subsys.intcon.s_axi_int_wready_pb1;
	assign axi_pb1_probe.bresp = subsys.intcon.s_axi_int_bresp_pb1;
	assign axi_pb1_probe.bvalid = subsys.intcon.s_axi_int_bvalid_pb1;
	assign axi_pb1_probe.bready = subsys.intcon.s_axi_int_bready_pb1;
	assign axi_pb1_probe.araddr = subsys.intcon.s_axi_int_araddr_pb1;
	assign axi_pb1_probe.arlen = subsys.intcon.s_axi_int_arlen_pb1;
	assign axi_pb1_probe.arsize = subsys.intcon.s_axi_int_arsize_pb1;
	assign axi_pb1_probe.arburst = subsys.intcon.s_axi_int_arburst_pb1;
	assign axi_pb1_probe.arvalid = subsys.intcon.s_axi_int_arvalid_pb1;
	assign axi_pb1_probe.arready = subsys.intcon.s_axi_int_arready_pb1;
	assign axi_pb1_probe.rdata = subsys.intcon.s_axi_int_rdata_pb1;
	assign axi_pb1_probe.rresp = subsys.intcon.s_axi_int_rresp_pb1;
	assign axi_pb1_probe.rlast = subsys.intcon.s_axi_int_rlast_pb1;
	assign axi_pb1_probe.rvalid = subsys.intcon.s_axi_int_rvalid_pb1;
	assign axi_pb1_probe.rready = subsys.intcon.s_axi_int_rready_pb1;

	assign axi_pp_probe.awaddr = subsys.intcon.s_axi_int_awaddr_pp;
	assign axi_pp_probe.awlen = subsys.intcon.s_axi_int_awlen_pp;
	assign axi_pp_probe.awsize = subsys.intcon.s_axi_int_awsize_pp;
	assign axi_pp_probe.awburst = subsys.intcon.s_axi_int_awburst_pp;
	assign axi_pp_probe.awvalid = subsys.intcon.s_axi_int_awvalid_pp;
	assign axi_pp_probe.awready = subsys.intcon.s_axi_int_awready_pp;
	assign axi_pp_probe.wstrb = subsys.intcon.s_axi_int_wstrb_pp;
	assign axi_pp_probe.wlast = subsys.intcon.s_axi_int_wlast_pp;
	assign axi_pp_probe.wvalid = subsys.intcon.s_axi_int_wvalid_pp;
	assign axi_pp_probe.wready = subsys.intcon.s_axi_int_wready_pp;
	assign axi_pp_probe.bresp = subsys.intcon.s_axi_int_bresp_pp;
	assign axi_pp_probe.bvalid = subsys.intcon.s_axi_int_bvalid_pp;
	assign axi_pp_probe.bready = subsys.intcon.s_axi_int_bready_pp;
	assign axi_pp_probe.araddr = subsys.intcon.s_axi_int_araddr_pp;
	assign axi_pp_probe.arlen = subsys.intcon.s_axi_int_arlen_pp;
	assign axi_pp_probe.arsize = subsys.intcon.s_axi_int_arsize_pp;
	assign axi_pp_probe.arburst = subsys.intcon.s_axi_int_arburst_pp;
	assign axi_pp_probe.arvalid = subsys.intcon.s_axi_int_arvalid_pp;
	assign axi_pp_probe.arready = subsys.intcon.s_axi_int_arready_pp;
	assign axi_pp_probe.rdata = subsys.intcon.s_axi_int_rdata_pp;
	assign axi_pp_probe.rresp = subsys.intcon.s_axi_int_rresp_pp;
	assign axi_pp_probe.rlast = subsys.intcon.s_axi_int_rlast_pp;
	assign axi_pp_probe.rvalid = subsys.intcon.s_axi_int_rvalid_pp;
	assign axi_pp_probe.rready = subsys.intcon.s_axi_int_rready_pp;

	assign axi_inmem_probe.awaddr = subsys.intcon.m_axi_int_awaddr_inmem;
	assign axi_inmem_probe.awlen = subsys.intcon.m_axi_int_awlen_inmem;
	assign axi_inmem_probe.awsize = subsys.intcon.m_axi_int_awsize_inmem;
	assign axi_inmem_probe.awburst = subsys.intcon.m_axi_int_awburst_inmem;
	assign axi_inmem_probe.awvalid = subsys.intcon.m_axi_int_awvalid_inmem;
	assign axi_inmem_probe.awready = subsys.intcon.m_axi_int_awready_inmem;
	assign axi_inmem_probe.wstrb = subsys.intcon.m_axi_int_wstrb_inmem;
	assign axi_inmem_probe.wlast = subsys.intcon.m_axi_int_wlast_inmem;
	assign axi_inmem_probe.wvalid = subsys.intcon.m_axi_int_wvalid_inmem;
	assign axi_inmem_probe.wready = subsys.intcon.m_axi_int_wready_inmem;
	assign axi_inmem_probe.bresp = subsys.intcon.m_axi_int_bresp_inmem;
	assign axi_inmem_probe.bvalid = subsys.intcon.m_axi_int_bvalid_inmem;
	assign axi_inmem_probe.bready = subsys.intcon.m_axi_int_bready_inmem;
	assign axi_inmem_probe.araddr = subsys.intcon.m_axi_int_araddr_inmem;
	assign axi_inmem_probe.arlen = subsys.intcon.m_axi_int_arlen_inmem;
	assign axi_inmem_probe.arsize = subsys.intcon.m_axi_int_arsize_inmem;
	assign axi_inmem_probe.arburst = subsys.intcon.m_axi_int_arburst_inmem;
	assign axi_inmem_probe.arvalid = subsys.intcon.m_axi_int_arvalid_inmem;
	assign axi_inmem_probe.arready = subsys.intcon.m_axi_int_arready_inmem;
	assign axi_inmem_probe.rdata = subsys.intcon.m_axi_int_rdata_inmem;
	assign axi_inmem_probe.rresp = subsys.intcon.m_axi_int_rresp_inmem;
	assign axi_inmem_probe.rlast = subsys.intcon.m_axi_int_rlast_inmem;
	assign axi_inmem_probe.rvalid = subsys.intcon.m_axi_int_rvalid_inmem;
	assign axi_inmem_probe.rready = subsys.intcon.m_axi_int_rready_inmem;

	assign axi_outmem_probe.awaddr = subsys.intcon.m_axi_int_awaddr_outmem;
	assign axi_outmem_probe.awlen = subsys.intcon.m_axi_int_awlen_outmem;
	assign axi_outmem_probe.awsize = subsys.intcon.m_axi_int_awsize_outmem;
	assign axi_outmem_probe.awburst = subsys.intcon.m_axi_int_awburst_outmem;
	assign axi_outmem_probe.awvalid = subsys.intcon.m_axi_int_awvalid_outmem;
	assign axi_outmem_probe.awready = subsys.intcon.m_axi_int_awready_outmem;
	assign axi_outmem_probe.wstrb = subsys.intcon.m_axi_int_wstrb_outmem;
	assign axi_outmem_probe.wlast = subsys.intcon.m_axi_int_wlast_outmem;
	assign axi_outmem_probe.wvalid = subsys.intcon.m_axi_int_wvalid_outmem;
	assign axi_outmem_probe.wready = subsys.intcon.m_axi_int_wready_outmem;
	assign axi_outmem_probe.bresp = subsys.intcon.m_axi_int_bresp_outmem;
	assign axi_outmem_probe.bvalid = subsys.intcon.m_axi_int_bvalid_outmem;
	assign axi_outmem_probe.bready = subsys.intcon.m_axi_int_bready_outmem;
	assign axi_outmem_probe.araddr = subsys.intcon.m_axi_int_araddr_outmem;
	assign axi_outmem_probe.arlen = subsys.intcon.m_axi_int_arlen_outmem;
	assign axi_outmem_probe.arsize = subsys.intcon.m_axi_int_arsize_outmem;
	assign axi_outmem_probe.arburst = subsys.intcon.m_axi_int_arburst_outmem;
	assign axi_outmem_probe.arvalid = subsys.intcon.m_axi_int_arvalid_outmem;
	assign axi_outmem_probe.arready = subsys.intcon.m_axi_int_arready_outmem;
	assign axi_outmem_probe.rdata = subsys.intcon.m_axi_int_rdata_outmem;
	assign axi_outmem_probe.rresp = subsys.intcon.m_axi_int_rresp_outmem;
	assign axi_outmem_probe.rlast = subsys.intcon.m_axi_int_rlast_outmem;
	assign axi_outmem_probe.rvalid = subsys.intcon.m_axi_int_rvalid_outmem;
	assign axi_outmem_probe.rready = subsys.intcon.m_axi_int_rready_outmem;

	assign axi_reg_probe.awaddr = subsys.intcon.m_axi_int_awaddr_reg;
	assign axi_reg_probe.awlen = subsys.intcon.m_axi_int_awlen_reg;
	assign axi_reg_probe.awsize = subsys.intcon.m_axi_int_awsize_reg;
	assign axi_reg_probe.awburst = subsys.intcon.m_axi_int_awburst_reg;
	assign axi_reg_probe.awvalid = subsys.intcon.m_axi_int_awvalid_reg;
	assign axi_reg_probe.awready = subsys.intcon.m_axi_int_awready_reg;
	assign axi_reg_probe.wstrb = subsys.intcon.m_axi_int_wstrb_reg;
	assign axi_reg_probe.wlast = subsys.intcon.m_axi_int_wlast_reg;
	assign axi_reg_probe.wvalid = subsys.intcon.m_axi_int_wvalid_reg;
	assign axi_reg_probe.wready = subsys.intcon.m_axi_int_wready_reg;
	assign axi_reg_probe.bresp = subsys.intcon.m_axi_int_bresp_reg;
	assign axi_reg_probe.bvalid = subsys.intcon.m_axi_int_bvalid_reg;
	assign axi_reg_probe.bready = subsys.intcon.m_axi_int_bready_reg;
	assign axi_reg_probe.araddr = subsys.intcon.m_axi_int_araddr_reg;
	assign axi_reg_probe.arlen = subsys.intcon.m_axi_int_arlen_reg;
	assign axi_reg_probe.arsize = subsys.intcon.m_axi_int_arsize_reg;
	assign axi_reg_probe.arburst = subsys.intcon.m_axi_int_arburst_reg;
	assign axi_reg_probe.arvalid = subsys.intcon.m_axi_int_arvalid_reg;
	assign axi_reg_probe.arready = subsys.intcon.m_axi_int_arready_reg;
	assign axi_reg_probe.rdata = subsys.intcon.m_axi_int_rdata_reg;
	assign axi_reg_probe.rresp = subsys.intcon.m_axi_int_rresp_reg;
	assign axi_reg_probe.rlast = subsys.intcon.m_axi_int_rlast_reg;
	assign axi_reg_probe.rvalid = subsys.intcon.m_axi_int_rvalid_reg;
	assign axi_reg_probe.rready = subsys.intcon.m_axi_int_rready_reg;

	assign axi_exreg_probe.awaddr = subsys.intcon.m_axi_int_awaddr_exreg;
	assign axi_exreg_probe.awlen = subsys.intcon.m_axi_int_awlen_exreg;
	assign axi_exreg_probe.awsize = subsys.intcon.m_axi_int_awsize_exreg;
	assign axi_exreg_probe.awburst = subsys.intcon.m_axi_int_awburst_exreg;
	assign axi_exreg_probe.awvalid = subsys.intcon.m_axi_int_awvalid_exreg;
	assign axi_exreg_probe.awready = subsys.intcon.m_axi_int_awready_exreg;
	assign axi_exreg_probe.wstrb = subsys.intcon.m_axi_int_wstrb_exreg;
	assign axi_exreg_probe.wlast = subsys.intcon.m_axi_int_wlast_exreg;
	assign axi_exreg_probe.wvalid = subsys.intcon.m_axi_int_wvalid_exreg;
	assign axi_exreg_probe.wready = subsys.intcon.m_axi_int_wready_exreg;
	assign axi_exreg_probe.bresp = subsys.intcon.m_axi_int_bresp_exreg;
	assign axi_exreg_probe.bvalid = subsys.intcon.m_axi_int_bvalid_exreg;
	assign axi_exreg_probe.bready = subsys.intcon.m_axi_int_bready_exreg;
	assign axi_exreg_probe.araddr = subsys.intcon.m_axi_int_araddr_exreg;
	assign axi_exreg_probe.arlen = subsys.intcon.m_axi_int_arlen_exreg;
	assign axi_exreg_probe.arsize = subsys.intcon.m_axi_int_arsize_exreg;
	assign axi_exreg_probe.arburst = subsys.intcon.m_axi_int_arburst_exreg;
	assign axi_exreg_probe.arvalid = subsys.intcon.m_axi_int_arvalid_exreg;
	assign axi_exreg_probe.arready = subsys.intcon.m_axi_int_arready_exreg;
	assign axi_exreg_probe.rdata = subsys.intcon.m_axi_int_rdata_exreg;
	assign axi_exreg_probe.rresp = subsys.intcon.m_axi_int_rresp_exreg;
	assign axi_exreg_probe.rlast = subsys.intcon.m_axi_int_rlast_exreg;
	assign axi_exreg_probe.rvalid = subsys.intcon.m_axi_int_rvalid_exreg;
	assign axi_exreg_probe.rready = subsys.intcon.m_axi_int_rready_exreg;
endmodule