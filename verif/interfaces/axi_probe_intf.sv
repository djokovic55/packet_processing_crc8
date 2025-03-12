
interface axi_probe_intf;
	logic[31:0] awaddr;
	logic[7:0] awlen;
	logic[2:0] awsize;
	logic[1:0] awburst;
	logic awvalid;
	logic awready;

	logic[31:0] wdata;
	logic[4:0] wstrb;
	logic wlast;
	logic wvalid;
	logic wready;

	logic[1:0] bresp;
	logic bvalid;
	logic bready;

	logic[31:0] araddr;
	logic[7:0] arlen;
	logic[2:0] arsize;
	logic[1:0] arburst;
	logic arvalid;
	logic arready;

	logic[31:0] rdata;
	logic[1:0] rresp;
	logic rlast;
	logic rvalid;
	logic rready;
    `define axi_probe_intf_fields \
	awaddr, awlen, awsize, awburst, awvalid, awready, wdata, wstrb, wlast, wvalid, wready, \
	bresp, bvalid, bready, araddr, arlen, arsize, arburst, arvalid, arready, \
	rdata, rresp, rlast, rvalid, rready
    modport driver  (output `axi_probe_intf_fields);
    modport monitor  (input `axi_probe_intf_fields);
endinterface