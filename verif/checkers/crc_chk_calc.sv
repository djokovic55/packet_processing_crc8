module crc_chk_calc (
	input[7:0] crc_in,
	input[7:0] data_in, 
	output[7:0] crc_out 
);

			assign crc_out[0] = crc_in[0] ^ crc_in[6] ^ crc_in[7] ^ data_in[0] ^ data_in[6] ^ data_in[7];
			assign crc_out[1] = crc_in[0] ^ crc_in[1] ^ crc_in[6] ^ data_in[0] ^ data_in[1] ^ data_in[6];
			assign crc_out[2] = crc_in[0] ^ crc_in[1] ^ crc_in[2] ^ crc_in[6] ^ data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[6];
			assign crc_out[3] = crc_in[1] ^ crc_in[2] ^ crc_in[3] ^ crc_in[7] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[7];
			assign crc_out[4] = crc_in[2] ^ crc_in[3] ^ crc_in[4] ^ data_in[2] ^ data_in[3] ^ data_in[4];
			assign crc_out[5] = crc_in[3] ^ crc_in[4] ^ crc_in[5] ^ data_in[3] ^ data_in[4] ^ data_in[5];
			assign crc_out[6] = crc_in[4] ^ crc_in[5] ^ crc_in[6] ^ data_in[4] ^ data_in[5] ^ data_in[6];
			assign crc_out[7] = crc_in[5] ^ crc_in[6] ^ crc_in[7] ^ data_in[5] ^ data_in[6] ^ data_in[7];

endmodule







