
interface regs_prot_intf;
	logic pb0_start_top;
	logic pb0_busy_top;
	logic pb0_irq_top;
	logic[31:0] pb0_addr_in_top;
	logic[3:0] pb0_byte_cnt_top;
	logic[3:0] pb0_pkt_type_top;
	logic pb0_ecc_en_top;
	logic pb0_crc_en_top;
	logic[1:0] pb0_ins_ecc_err_top;
	logic pb0_ins_crc_err_top;
	logic[3:0] pb0_ecc_val_top;
	logic[7:0] pb0_crc_val_top;
	logic[2:0] pb0_sop_val_top;
	logic[3:0] pb0_data_sel_top;
	logic[31:0] pb0_addr_out_top;

	logic pb1_start_top;
	logic pb1_busy_top;
	logic pb1_irq_top;
	logic[31:0] pb1_addr_in_top;
	logic[3:0] pb1_byte_cnt_top;
	logic[3:0] pb1_pkt_type_top;
	logic pb1_ecc_en_top;
	logic pb1_crc_en_top;
	logic[1:0] pb1_ins_ecc_err_top;
	logic pb1_ins_crc_err_top;
	logic[3:0] pb1_ecc_val_top;
	logic[7:0] pb1_crc_val_top;
	logic[2:0] pb1_sop_val_top;
	logic[3:0] pb1_data_sel_top;
	logic[31:0] pb1_addr_out_top;

	logic pp_start_top;
	logic pp_busy_top;
	logic pp_irq_top;
	logic[31:0] pp_addr_hdr_top;
	logic pp_ignore_ecc_err_top;
	logic pp_pkt_ecc_corr_top;
	logic pp_pkt_ecc_uncorr_top;
	logic pp_pkt_crc_err_top;
	logic[3:0] pp_pkt_byte_cnt_top;
	logic[3:0] pp_pkt_type_top;

    `define regs_port_intf_fields \
	pb0_start_top, pb0_busy_top, pb0_irq_top, pb0_addr_in_top, pb0_byte_cnt_top, pb0_pkt_type_top, pb0_ecc_en_top, pb0_crc_en_top, pb0_ins_ecc_err_top, pb0_ins_crc_err_top, pb0_ecc_val_top, pb0_crc_val_top, pb0_sop_val_top, pb0_data_sel_top, pb0_addr_out_top, \
    pb1_start_top, pb1_busy_top, pb1_irq_top, pb1_addr_in_top, pb1_byte_cnt_top, pb1_pkt_type_top, pb1_ecc_en_top, pb1_crc_en_top, pb1_ins_ecc_err_top, pb1_ins_crc_err_top, pb1_ecc_val_top, pb1_crc_val_top, pb1_sop_val_top, pb1_data_sel_top, pb1_addr_out_top, \
    pp_start_top, pp_busy_top, pp_irq_top, pp_addr_hdr_top, pp_ignore_ecc_err_top, pp_pkt_ecc_corr_top, pp_pkt_ecc_uncorr_top, pp_pkt_crc_err_top, pp_pkt_byte_cnt_top, pp_pkt_type_top
    modport driver  (output `regs_port_intf_fields);
    modport monitor (input `regs_port_intf_fields);
endinterface