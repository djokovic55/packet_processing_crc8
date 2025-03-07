
interface pp_conf_port_intf;
	logic pp_irq;
	logic [31:0] pp_addr_hdr;
	logic pp_ignore_ecc_err;
    `define pp_conf_port_intf_fields \
        pp_irq, pp_addr_hdr, pp_ignore_ecc_err
    modport driver  (output `pp_conf_port_intf_fields);
    modport monitor (input `pp_conf_port_intf_fields);
endinterface