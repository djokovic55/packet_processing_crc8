interface pb_regs_port_intf;
	logic pb_start;
	logic pb_busy;
	logic pb_irq;
	logic[31:0] pb_addr_in;
	logic[3:0] pb_byte_cnt;
	logic[3:0] pb_pkt_type;
	logic pb_ecc_en;
	logic pb_crc_en;
	logic pb_ins_ecc_err;
	logic pb_ins_crc_err;
	logic[3:0] pb_ecc_val;
	logic[7:0] pb_crc_val;
	logic[2:0] pb_sop_val;
	logic[3:0] pb_data_sel;
	logic[31:0] pb_addr_out;

    `define pb_regs_port_intf_fields \
	pb_start, pb_busy, pb_irq, pb_addr_in, pb_byte_cnt, pb_pkt_type, pb_ecc_en, pb_crc_en, pb_ins_ecc_err, pb_ins_crc_err, pb_ecc_val, pb_crc_val, pb_sop_val, pb_data_sel, pb_addr_out
    modport driver  (output `pb_regs_port_intf_fields);
    modport monitor (input `pb_regs_port_intf_fields);
endinterface

interface pp_regs_port_intf;

	logic pp_start;
	logic pp_busy;
	logic pp_irq;
	logic[31:0] pp_addr_hdr;
	logic pp_ignore_ecc_err;
	logic pp_pkt_ecc_corr;
	logic pp_pkt_ecc_uncorr;
	logic pp_pkt_crc_err;
	logic[3:0] pp_pkt_byte_cnt;
	logic[3:0] pp_pkt_type;

    `define pp_regs_port_intf_fields \
    pp_start, pp_busy, pp_irq, pp_addr_hdr, pp_ignore_ecc_err, pp_pkt_ecc_corr, pp_pkt_ecc_uncorr, pp_pkt_crc_err, pp_pkt_byte_cnt, pp_pkt_type
    modport driver  (output `pp_regs_port_intf_fields);
    modport monitor (input `pp_regs_port_intf_fields);
endinterface
