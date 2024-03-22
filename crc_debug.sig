<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>24</insertion-point-position>
  <wave>
    <expr>chk_top.clk</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>crc_debug::top.chk_top.ast_crc_err_when_ecc_err_exists</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>crc_debug::top.chk_top.ast_crc_no_err</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.crc_err_reg</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.pp_irq_top</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.pp_pkt_crc_err_top</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.pp_pkt_ecc_uncorr_top</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.reset</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>clk</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.clk</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.pp_pkt_crc_err_top</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr/>
    <label>CRC_CHECKER</label>
    <wave collapsed="true">
      <expr>chk_top.state_reg</expr>
      <label/>
      <radix>chk_top.state_reg</radix>
    </wave>
    <wave collapsed="true">
      <expr>chk_top.inmem_addr_b_i</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_top.inmem_data_b_o</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_top.byte_cnt_reg</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_top.crc_ext_reg</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_top.crc_calc_reg</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <wave>
    <expr>chk_top.crc_err_reg</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>chk_top.crc_cnt_reg</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.pp_irq_top</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.corr_err_irq_pulse</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.corr_err_irq_reg2</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.corr_err_irq_reg</expr>
    <label/>
    <radix/>
  </wave>
  <spacer/>
  <group collapsed="false">
    <expr/>
    <label>PARSER</label>
    <wave collapsed="true">
      <expr>subsys.parser.state_reg</expr>
      <label/>
      <radix>subsys.parser.state_reg</radix>
    </wave>
    <wave>
      <expr>subsys.parser.pkt_ecc_corr_o</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>subsys.parser.pkt_ecc_uncorr_o</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>subsys.parser.pkt_byte_cnt_o</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>subsys.parser.M_AXI_ARADDR</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>inmem.inmem_bram.ram_s(8)</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>subsys.parser.M_AXI_RDATA</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>subsys.parser.master_axi_cont_ctrl.axi_araddr</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>inmem.slave_axi_cont_inmem.axi_araddr</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>inmem.slave_axi_cont_inmem.axi_araddr(31 downto 2)</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>subsys.parser.M_AXI_RVALID</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>subsys.parser.M_AXI_RLAST</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>subsys.parser.crc_out_s</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>subsys.parser.crc_reg</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>subsys.parser.crc_err_s</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>subsys.parser.fifo_in.read_index_s</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>subsys.parser.fifo_in.write_index_s</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <spacer/>
  <wave collapsed="true">
    <expr>subsys.parser.fifo_in.fifo_data_s(0)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.parser.fifo_in.fifo_data_s(1)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.parser.fifo_in.fifo_data_s(2)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>chk_top.inmem_data_b_o</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>chk_top.pp_addr_hdr_top</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.pp_busy_top</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.inmem_we_b_i</expr>
    <label/>
    <radix/>
  </wave>
  <highlightlist>
    <!--Users can remove the highlightlist block if they want to load the signal save file into older version of Jasper-->
    <highlight>
      <expr>chk_top.byte_cnt_reg</expr>
      <color>builtin_blue</color>
    </highlight>
    <highlight>
      <expr>chk_top.pp_irq_top</expr>
      <color>builtin_green</color>
    </highlight>
    <highlight>
      <expr>subsys.parser.pkt_byte_cnt_o</expr>
      <color>builtin_blue</color>
    </highlight>
    <highlight>
      <expr>subsys.parser.pkt_ecc_corr_o</expr>
      <color>builtin_orange</color>
    </highlight>
    <highlight>
      <expr>subsys.parser.pkt_ecc_uncorr_o</expr>
      <color>builtin_red</color>
    </highlight>
  </highlightlist>
</wavelist>
