

interface inmem_port_b_intf;
	logic inmem_en_b_i;
	logic [31:0] inmem_data_b_i;
	logic [13:0] inmem_addr_b_i;
	logic inmem_we_b_i;
	logic [31:0] inmem_data_b_o;
    `define inmem_port_b_intf_fields \
    inmem_en_b_i, inmem_data_b_i, inmem_addr_b_i, inmem_we_b_i, inmem_data_b_o
    modport driver  (output `inmem_port_b_intf_fields);
    modport monitor (input `inmem_port_b_intf_fields);
endinterface