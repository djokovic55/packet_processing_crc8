module checker_crc(
  input clk,
  input reset,

  input[31:0] data_i,
  input[3:0] we_i,


);

	default clocking @(posedge clk);
	endclocking

	default disable iff reset;

	logic [7:0] crc_mem[19];

	logic [4:0] wr_ptr = 0;
	logic [4:0] rd_ptr = 0;

	logic [7:0] crc;

	logic re;
	logic data_o <= crc_mem(rd_ptr);

	// CRC_FIFO
	always @(posedge clk)
	begin
		if(we_i != 0) begin
			crc_mem(wr_ptr) <= data_i[7:0];
			crc_mem(wr_ptr+1) <= data_i[15:8];
			crc_mem(wr_ptr+2) <= data_i[23:16];
			crc_mem(wr_ptr+3) <= data_i[31:24];

			wr_ptr <= wr_ptr + 4;
		end

		if(re) begin
			rd_ptr <= rd_ptr + 1;
		end
	end
	



endchecker
