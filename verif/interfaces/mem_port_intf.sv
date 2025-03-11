

interface mem_port_intf;
	logic en;
	logic [31:0] data_i;
	logic [13:0] addr;
	logic [3:0] we;
	logic [31:0] data_o;
    `define inmem_port_b_intf_fields \
	en, data_i, addr, we, data_o 
	// All the fields of the interface are defined as output 
	// because fv_adapter should produce these values for other components
    modport driver  (output `inmem_port_b_intf_fields);
    modport monitor  (input `inmem_port_b_intf_fields);
endinterface