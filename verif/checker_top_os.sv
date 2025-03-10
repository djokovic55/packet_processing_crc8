
module  checker_top_os(
  ////////////////////////////////////////////////////////////////////////////////
  // Interface
  ////////////////////////////////////////////////////////////////////////////////

  input clk,
  input reset,

  // ex_reg top interface 

  ////////////////////////////////////////////////////////////////////////////////
  // Build task configuration
  ////////////////////////////////////////////////////////////////////////////////
  input pb_irq,
  input[31:0] pb_addr_in, // assumed
  input[3:0] pb_byte_cnt,// assumed
  input[3:0] pb_pkt_type,
  input pb_ecc_en,
  input pb_crc_en,
  input pb_ins_ecc_err,
  input pb_ins_crc_err,
  input[3:0] pb_ecc_val,
  input[7:0] pb_crc_val,
  input[2:0] pb_sop_val,
  input[3:0] pb_data_sel,// assumed
  input[31:0] pb_addr_out,// assumed

  ////////////////////////////////////////////////////////////////////////////////
  // Parse task configuration
  ////////////////////////////////////////////////////////////////////////////////
  input pp_irq,
  input[31:0] pp_addr_hdr,
  input pp_ignore_ecc_err,

  ////////////////////////////////////////////////////////////////////////////////
  // Inmem port B top interface, used for memory configuration
  ////////////////////////////////////////////////////////////////////////////////
  input inmem_en_b_i,
  input[31:0] inmem_data_b_i,
  input[13:0] inmem_addr_b_i,
  input inmem_we_b_i,
  input[31:0] inmem_data_b_o,

  ////////////////////////////////////////////////////////////////////////////////
  // Outmem port B top interface, memory read only
  ////////////////////////////////////////////////////////////////////////////////
  input outmem_en_b_i,
  input[31:0] outmem_data_b_i,
  input[13:0] outmem_addr_b_i,
  input outmem_we_b_i,
  input[31:0] outmem_data_b_o,

  ////////////////////////////////////////////////////////////////////////////////
  // Controller's status signal
  ////////////////////////////////////////////////////////////////////////////////
  input cont_busy_top,

  ////////////////////////////////////////////////////////////////////////////////
  // regs top interface
  ////////////////////////////////////////////////////////////////////////////////

  input pb0_start_top,
  input pb0_busy_top,
  input pb0_irq_top,
  input[31:0] pb0_addr_in_top,
  input[3:0] pb0_byte_cnt_top,
  input[3:0] pb0_pkt_type_top,
  input pb0_ecc_en_top,
  input pb0_crc_en_top,
  input[1:0] pb0_ins_ecc_err_top,
  input pb0_ins_crc_err_top,
  input[3:0] pb0_ecc_val_top,
  input[7:0] pb0_crc_val_top,
  input[2:0] pb0_sop_val_top,
  input[3:0] pb0_data_sel_top,
  input[31:0] pb0_addr_out_top,

  input pb1_start_top,
  input pb1_busy_top,
  input pb1_irq_top,
  input[31:0] pb1_addr_in_top,
  input[3:0] pb1_byte_cnt_top,
  input[3:0] pb1_pkt_type_top,
  input pb1_ecc_en_top,
  input pb1_crc_en_top,
  input[1:0] pb1_ins_ecc_err_top,
  input pb1_ins_crc_err_top,
  input[3:0] pb1_ecc_val_top,
  input[7:0] pb1_crc_val_top,
  input[2:0] pb1_sop_val_top,
  input[3:0] pb1_data_sel_top,
  input[31:0] pb1_addr_out_top,

  input pp_start_top,
  input pp_busy_top,
  input pp_irq_top,
  input[31:0] pp_addr_hdr_top,
  input pp_ignore_ecc_err_top,
  input pp_pkt_ecc_corr_top,
  input pp_pkt_ecc_uncorr_top,
  input pp_pkt_crc_err_top,
  input[3:0] pp_pkt_byte_cnt_top,
  input[3:0] pp_pkt_type_top
);

  default 
  clocking @(posedge clk);
  endclocking

  default disable iff reset;

  ////////////////////////////////////////////////////////////////////////////////
  // Build task constraints
  ////////////////////////////////////////////////////////////////////////////////

  asm_addr_in_stability:                assume property($stable(pb_addr_in));
  asm_max_byte_cnt_stability:           assume property($stable(pb_byte_cnt));
  asm_merg_op_stability:                assume property($stable(pb_data_sel));
  asm_crc_en_stability:                 assume property($stable(pb_crc_en));
  asm_ecc_en_stability:                 assume property($stable(pb_ecc_en));
  asm_pkt_type_stability:               assume property($stable(pb_pkt_type));
  asm_ins_ecc_err_stability:            assume property($stable(pb_ins_ecc_err));
  asm_ins_crc_err_stability:            assume property($stable(pb_ins_crc_err));
  asm_ecc_val_stability:                assume property($stable(pb_ecc_val));
  asm_crc_val_stability:                assume property($stable(pb_crc_val));
  asm_sop_val_stability:                assume property($stable(pb_sop_val));
  asm_addr_out_stability:               assume property($stable(pb_addr_out));

  asm_addr_in:                          assume property(pb_addr_in[31:4] == '0);
  asm_inmem_bound:                      assume property(pb_byte_cnt + pb_addr_in <= 18);
  asm_outmem_bound:                     assume property(pb_byte_cnt + pb_addr_out + 3 <= 18);
  asm_addr_out:                         assume property(pb_addr_out[31:4] == '0);
  asm_merging_option:                   assume property(pb_data_sel inside {4'h0, 4'h1, 4'h2});

  ////////////////////////////////////////////////////////////////////////////////
  // Parse task constraints
  ////////////////////////////////////////////////////////////////////////////////

  asm_addr_hdr_i_stability:             assume property ($stable(pp_addr_hdr));
  asm_ignore_ecc_err_stability:         assume property ($stable(pp_ignore_ecc_err));

  asm_addr_hdr_i:                       assume property (pp_addr_hdr[31:4] == '0);

  ////////////////////////////////////////////////////////////////////////////////
  // Top covers
  ////////////////////////////////////////////////////////////////////////////////

  cov_pb0_start:                        cover property(pb0_start_top == 1'b1);
  cov_pb0_end:                          cover property(pb0_irq_top == 1'b1);
  cov_pb0_start_byte_cnt0:              cover property(pb0_start_top == 1'b1 && pb0_byte_cnt_top == 4'h0);
  cov_pb0_start_byte_cnt7:              cover property(pb0_start_top == 1'b1 && pb0_byte_cnt_top == 4'h7);
  cov_pb1_start:                        cover property(pb1_start_top == 1'b1);
  cov_pb1_end:                          cover property(pb1_irq_top == 1'b1);
  cov_pp_start:                         cover property(pp_start_top == 1'b1);
  cov_pp_end:                           cover property(pp_irq_top == 1'b1);
  cov_pp_start_byte_cnt5:               cover property(pp_start_top == 1'b1 && pp_pkt_byte_cnt_top == 4'h5);
  cov_pp_byte_cnt5:                     cover property(pp_pkt_byte_cnt_top == 4'h5);
  cov_ecc_corr_err:                     cover property(pp_pkt_ecc_corr_top == 1'b1);
  cov_no_ecc_corr_err:                  cover property(pp_pkt_ecc_corr_top == 1'b0);
  cov_ecc_uncorr_err:                   cover property(pp_pkt_ecc_uncorr_top == 1'b1);
  cov_no_ecc_uncorr_err:                cover property(pp_pkt_ecc_uncorr_top == 1'b0);
  cov_crc_err:                          cover property(pp_pkt_crc_err_top == 1'b1);
  cov_no_crc_err:                       cover property(pp_pkt_crc_err_top == 1'b0);

  //SECTION Cover points
//   cov_pp_pb0_work:                      cover property(!pp_busy_top && !pb0_busy_top);
//   cov_pp_pb1_work:                      cover property(!pp_busy_top && !pb1_busy_top);
//   cov_pb0_pb1_work:                     cover property(!pb1_busy_top && !pb0_busy_top);
//   cov_pb0_pb1_long_work:                cover property((!pb1_busy_top && !pb0_busy_top)[*5]);
//   cov_pb0_work:                         cover property(pb0_start_top);
//   cov_pb0_check:                        cover property((!pb0_busy_top && pb0_checker_en) ##[1:$] pb0_irq_top);
//   cov_pb1_check:                        cover property((!pb1_busy_top && pb1_checker_en) ##[1:$] pb1_irq_top);
//   cov_2pb0:                             cover property(pb0_irq_top[->2]);
//   cov_2pb1:                             cover property(pb0_irq_top[->2]);
//   cov_2pp:                              cover property(pb0_irq_top[->2]);

  ////////////////////////////////////////////////////////////////////////////////	
  // IMPORTANT Assert valid register values
  ////////////////////////////////////////////////////////////////////////////////	

  ast_top_reg_pb0_addr_in_lv4_help_high:              assert property(pb0_start_top |-> pb0_addr_in_top == pb_addr_in);
  ast_top_reg_pb0_byte_cnt_lv4_help_high:             assert property(pb0_start_top |-> pb0_byte_cnt_top == pb_byte_cnt);
  ast_top_reg_pb0_pkt_type_lv4_help_high:             assert property(pb0_start_top |-> pb0_pkt_type_top == pb_pkt_type);
  ast_top_reg_pb0_ecc_en_lv4_help_high:               assert property(pb0_start_top |-> pb0_ecc_en_top == pb_ecc_en);
  ast_top_reg_pb0_crc_en_lv4_help_high:               assert property(pb0_start_top |-> pb0_crc_en_top == pb_crc_en);
  ast_top_reg_pb0_ins_ecc_err_lv4_help_high:          assert property(pb0_start_top |-> pb0_ins_ecc_err_top == pb_ins_ecc_err);
  ast_top_reg_pb0_ins_crc_err_lv4_help_high:          assert property(pb0_start_top |-> pb0_ins_crc_err_top == pb_ins_crc_err);
  ast_top_reg_pb0_ecc_val_lv4_help_high:              assert property(pb0_start_top |-> pb0_ecc_val_top == pb_ecc_val);
  ast_top_reg_pb0_crc_val_lv4_help_high:              assert property(pb0_start_top |-> pb0_crc_val_top == pb_crc_val);
  ast_top_reg_pb0_sop_val_lv4_help_high:              assert property(pb0_start_top |-> pb0_sop_val_top == pb_sop_val);
  ast_top_reg_pb0_data_sel_lv4_help_high:             assert property(pb0_start_top |-> pb0_data_sel_top == pb_data_sel);
  ast_top_reg_pb0_addr_out_lv4_help_high:             assert property(pb0_start_top |-> pb0_addr_out_top == pb_addr_out);

  ast_top_reg_pb1_addr_in_lv4_help_high:              assert property(pb1_start_top |-> pb1_addr_in_top == pb_addr_in);
  ast_top_reg_pb1_byte_cnt_lv4_help_high:             assert property(pb1_start_top |-> pb1_byte_cnt_top == pb_byte_cnt);
  ast_top_reg_pb1_pkt_type_lv4_help_high:             assert property(pb1_start_top |-> pb1_pkt_type_top == pb_pkt_type);
  ast_top_reg_pb1_ecc_en_lv4_help_high:               assert property(pb1_start_top |-> pb1_ecc_en_top == pb_ecc_en);
  ast_top_reg_pb1_crc_en_lv4_help_high:               assert property(pb1_start_top |-> pb1_crc_en_top == pb_crc_en);
  ast_top_reg_pb1_ins_ecc_err_lv4_help_high:          assert property(pb1_start_top |-> pb1_ins_ecc_err_top == pb_ins_ecc_err);
  ast_top_reg_pb1_ins_crc_err_lv4_help_high:          assert property(pb1_start_top |-> pb1_ins_crc_err_top == pb_ins_crc_err);
  ast_top_reg_pb1_ecc_val_lv4_help_high:              assert property(pb1_start_top |-> pb1_ecc_val_top == pb_ecc_val);
  ast_top_reg_pb1_crc_val_lv4_help_high:              assert property(pb1_start_top |-> pb1_crc_val_top == pb_crc_val);
  ast_top_reg_pb1_sop_val_lv4_help_high:              assert property(pb1_start_top |-> pb1_sop_val_top == pb_sop_val);
  ast_top_reg_pb1_data_sel_lv4_help_high:             assert property(pb1_start_top |-> pb1_data_sel_top == pb_data_sel);
  ast_top_reg_pb1_addr_out_lv4_help_high:             assert property(pb1_start_top |-> pb1_addr_out_top == pb_addr_out);

  ast_top_reg_pp_addr_hdr_lv4_help_high:              assert property(pp_start_top |-> pp_addr_hdr_top == pp_addr_hdr);
  ast_top_reg_pp_ignore_ecc_err_lv4_help_high:        assert property(pp_start_top |-> pp_ignore_ecc_err_top == pp_ignore_ecc_err);

endmodule
