
interface pb_conf_port_intf;

    logic pb_irq;
    logic [31:0] pb_addr_in; 
    logic [3:0] pb_byte_cnt;
    logic [3:0] pb_pkt_type;
    logic pb_ecc_en;
    logic pb_crc_en;
    logic pb_ins_ecc_err;
    logic pb_ins_crc_err;
    logic [3:0] pb_ecc_val;
    logic [7:0] pb_crc_val;
    logic [2:0] pb_sop_val;
    logic [3:0] pb_data_sel;
    logic [31:0] pb_addr_out;

    `define pb_conf_port_intf_fields \
        pb_irq, pb_addr_in, pb_byte_cnt, pb_pkt_type, \
        pb_ecc_en, pb_crc_en, pb_ins_ecc_err, pb_ins_crc_err, \
        pb_ecc_val, pb_crc_val, pb_sop_val, pb_data_sel, pb_addr_out

    modport driver (output `pb_conf_port_intf_fields);
    modport monitor (input `pb_conf_port_intf_fields);

endinterface