
checker  checker_top(
  clk,
  reset,

  // ex_reg top interface 
  pb_irq,
  pb_addr_in,
  pb_byte_cnt,
  pb_pkt_type,
  pb_ecc_en,
  pb_crc_en,
  pb_ins_ecc_err,
  pb_ins_crc_err,
  pb_ecc_val,
  pb_crc_val,
  pb_sop_val,
  pb_data_sel,
  pb_addr_out,
  pp_irq,
  pp_addr_hdr,
  pp_ignore_ecc_err,

  // inmem port B top interface, used for memory configuration
  inmem_en_b_i,
  inmem_data_b_i,
  inmem_addr_b_i,
  inmem_we_b_i,
  inmem_data_b_o,

  // outmem port B top interface, memory read only
  outmem_en_b_i,
  outmem_data_b_i,
  outmem_addr_b_i,
  outmem_we_b_i,
  outmem_data_b_o,

  // regs top interface
  pb0_start_top,
  pb0_busy_top,
  pb0_irq_top,
  pb0_addr_in_top,
  pb0_byte_cnt_top,
  pb0_pkt_type_top,
  pb0_ecc_en_top,
  pb0_crc_en_top,
  pb0_ins_ecc_err_top,
  pb0_ins_crc_err_top,
  pb0_ecc_val_top,
  pb0_crc_val_top,
  pb0_sop_val_top,
  pb0_data_sel_top,
  pb0_addr_out_top,
  pb1_start_top,
  pb1_busy_top,
  pb1_irq_top,
  pb1_addr_in_top,
  pb1_byte_cnt_top,
  pb1_pkt_type_top,
  pb1_ecc_en_top,
  pb1_crc_en_top,
  pb1_ins_ecc_err_top,
  pb1_ins_crc_err_top,
  pb1_ecc_val_top,
  pb1_crc_val_top,
  pb1_sop_val_top,
  pb1_data_sel_top,
  pb1_addr_out_top,
  pp_start_top,
  pp_busy_top,
  pp_irq_top,
  pp_addr_hdr_top,
  pp_ignore_ecc_err_top,
  pp_pkt_ecc_corr_top,
  pp_pkt_ecc_uncorr_top,
  pp_pkt_crc_err_top,
  pp_pkt_byte_cnt_top,
  pp_pkt_type_top
);

  default 
  clocking @(posedge clk);
  endclocking

  default disable iff reset;

  //SECTION EX_REGS Interface Config
  
  // Builder config
  asm_max_byte_cnt: assume property(pb_byte_cnt <= 4'hF);
  asm_min_byte_cnt: assume property(pb_byte_cnt >= 4'h0);
  asm_stable_max_byte_cnt: assume property($stable(pb_byte_cnt));

  // asm_merging_option: assume property(pb_data_sel inside {4'h0, 4'h1, 4'h2});
  asm_merging_option: assume property(pb_data_sel == 4'h2);
  asm_merg_op_stability: assume property($stable(pb_data_sel));

  asm_crc_en: assume property(pb_crc_en == 1'b1);
  asm_crc_en_stability: assume property($stable(pb_crc_en));
  asm_ecc_en: assume property(pb_ecc_en == 1'b1);
  asm_ecc_en_stability: assume property($stable(pb_ecc_en));

  asm_addr_in: assume property(pb_addr_in == 32'h1);
  asm_pkt_type: assume property(pb_pkt_type == 4'hA);
  asm_ins_ecc_err: assume property(pb_ins_ecc_err == 1'b0);
  asm_ins_crc_err: assume property(pb_ins_crc_err == 1'b0);
  asm_ecc_val: assume property(pb_ecc_val == 4'h0);
  asm_crc_val: assume property(pb_crc_val == 8'hCC);
  asm_sop_val: assume property(pb_sop_val == 3'h7);
  asm_addr_out: assume property(pb_addr_out == 32'h2);

  // Parser config
  asm_addr_hdr_i: assume property (pp_addr_hdr == 32'h2);
  asm_ignore_ecc_err: assume property (pp_ignore_ecc_err == 1'b0);

  // Cover
  cov_pb_irq: cover property(pb_irq[*5]);
  cov_pp_irq: cover property(pp_irq[*5]);


  //SECTION REGS Interface props
  cov_pb0_start: cover property(pb0_start_top == 1'b1);
  cov_pb1_start: cover property(pb1_start_top == 1'b1);
  cov_pp_start: cover property(pp_start_top == 1'b1);

  cov_pb0_start_byte_cnt0: cover property(pb0_start_top == 1'b1 && pb0_byte_cnt_top == 4'h0);
  cov_pb0_start_byte_cnt7: cover property(pb0_start_top == 1'b1 && pb0_byte_cnt_top == 4'h7);


  cov_ecc_corr_err: cover property(pp_pkt_ecc_corr_top == 1'b1);
  cov_ecc_uncorr_err: cover property(pp_pkt_ecc_uncorr_top == 1'b1);

    // IMPORTANT Assert valid register values

  ast_pb0_addr_in: assert property(pb0_start_top |-> pb0_addr_in_top == pb_addr_in);
  ast_pb0_byte_cnt: assert property(pb0_start_top |-> pb0_byte_cnt_top == pb_byte_cnt);
  ast_pb0_pkt_type: assert property(pb0_start_top |-> pb0_pkt_type_top == pb_pkt_type);
  ast_pb0_ecc_en: assert property(pb0_start_top |-> pb0_ecc_en_top == pb_ecc_en);
  ast_pb0_crc_en: assert property(pb0_start_top |-> pb0_crc_en_top == pb_crc_en);
  ast_pb0_ins_ecc_err: assert property(pb0_start_top |-> pb0_ins_ecc_err_top == pb_ins_ecc_err);
  ast_pb0_ins_crc_err: assert property(pb0_start_top |-> pb0_ins_crc_err_top == pb_ins_crc_err);
  ast_pb0_ecc_val: assert property(pb0_start_top |-> pb0_ecc_val_top == pb_ecc_val);
  ast_pb0_crc_val: assert property(pb0_start_top |-> pb0_crc_val_top == pb_crc_val);
  ast_pb0_sop_val: assert property(pb0_start_top |-> pb0_sop_val_top == pb_sop_val);
  ast_pb0_data_sel: assert property(pb0_start_top |-> pb0_data_sel_top == pb_data_sel);
  ast_pb0_addr_out: assert property(pb0_start_top |-> pb0_addr_out_top == pb_addr_out);

  ast_pb1_addr_in: assert property(pb1_start_top |-> pb1_addr_in_top == pb_addr_in);
  ast_pb1_byte_cnt: assert property(pb1_start_top |-> pb1_byte_cnt_top == pb_byte_cnt);
  ast_pb1_pkt_type: assert property(pb1_start_top |-> pb1_pkt_type_top == pb_pkt_type);
  ast_pb1_ecc_en: assert property(pb1_start_top |-> pb1_ecc_en_top == pb_ecc_en);
  ast_pb1_crc_en: assert property(pb1_start_top |-> pb1_crc_en_top == pb_crc_en);
  ast_pb1_ins_ecc_err: assert property(pb1_start_top |-> pb1_ins_ecc_err_top == pb_ins_ecc_err);
  ast_pb1_ins_crc_err: assert property(pb1_start_top |-> pb1_ins_crc_err_top == pb_ins_crc_err);
  ast_pb1_ecc_val: assert property(pb1_start_top |-> pb1_ecc_val_top == pb_ecc_val);
  ast_pb1_crc_val: assert property(pb1_start_top |-> pb1_crc_val_top == pb_crc_val);
  ast_pb1_sop_val: assert property(pb1_start_top |-> pb1_sop_val_top == pb_sop_val);
  ast_pb1_data_sel: assert property(pb1_start_top |-> pb1_data_sel_top == pb_data_sel);
  ast_pb1_addr_out: assert property(pb1_start_top |-> pb1_addr_out_top == pb_addr_out);

  ast_pp_addr_hdr: assert property(pp_start_top |-> pp_addr_hdr_top == pp_addr_hdr);
  ast_pp_ignore_ecc_err: assert property(pp_start_top |-> pp_ignore_ecc_err_top == pp_ignore_ecc_err);

  //SECTION INMEM Interface Port B props
  asm_inmem_en: assume property(inmem_en_b_i == 1'b1);
  asm_inmem_data_i: assume property(inmem_data_b_i == 32'hDEADBEEF);
  // asm_inmem_addr: assume property(inmem_addr_b_i == 14'h0);
  asm_inmem_we: assume property(inmem_we_b_i == 4'hf);
  // asm_inmem_data: assume property(inmem_data_b_o == 1'b1);

  //SECTION OUTMEM Interface Port B props
  // outmem port B top interface, memory read only
  asm_outmem_en: assume property(outmem_en_b_i == 1'b1);
  asm_outmem_data_i: assume property(outmem_data_b_i == 32'h0);
  // asm_outmem_addr: assume property(outmem_addr_b_i == 14'h1);
  asm_outmem_we: assume property(outmem_we_b_i == 1'b0);
  // asm_outmem_data: assume property(outmem_data_b_o == 1'b1);

  //IMPORTANT Assert data integrity 

endchecker
