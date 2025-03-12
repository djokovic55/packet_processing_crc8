
interface outmem_port_b_intf;
	logic outmem_en_b_i;
	logic [31:0] outmem_data_b_i;
	logic [13:0] outmem_addr_b_i;
	logic outmem_we_b_i;
	logic [31:0] outmem_data_b_o;
    `define outmem_port_b_intf_fields \
    outmem_en_b_i, outmem_data_b_i, outmem_addr_b_i, outmem_we_b_i, outmem_data_b_o
    modport driver  (output `outmem_port_b_intf_fields);
    modport monitor (input `outmem_port_b_intf_fields);
endinterface