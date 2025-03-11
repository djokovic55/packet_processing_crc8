
`include "pp_env_pkg.sv"
`include "interfaces/pp_conf_port_intf.sv"
`include "interfaces/pb_conf_port_intf.sv"
`include "interfaces/mem_port_intf.sv"
`include "interfaces/regs_port_intf.sv"
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
	pp_regs_port_intf.driver pp_regs_port
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

    assign pp_regs_port.pp_start_top = pp_start_top;
    assign pp_regs_port.pp_busy_top = pp_busy_top;
    assign pp_regs_port.pp_irq_top = pp_irq_top;
    assign pp_regs_port.pp_addr_hdr_top = pp_addr_hdr_top;
    assign pp_regs_port.pp_ignore_ecc_err_top = pp_ignore_ecc_err_top;
    assign pp_regs_port.pp_pkt_ecc_corr_top = pp_pkt_ecc_corr_top;
    assign pp_regs_port.pp_pkt_ecc_uncorr_top = pp_pkt_ecc_uncorr_top;
    assign pp_regs_port.pp_pkt_crc_err_top = pp_pkt_crc_err_top;
    assign pp_regs_port.pp_pkt_byte_cnt_top = pp_pkt_byte_cnt_top;
    assign pp_regs_port.pp_pkt_type_top = pp_pkt_type_top;


endmodule