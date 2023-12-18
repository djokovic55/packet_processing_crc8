<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>45</insertion-point-position>
  <group collapsed="false">
    <expr/>
    <label>Clocks Signals</label>
    <wave>
      <expr>clk</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>top_bad_machine.clk</expr>
      <label>top_bad_machine.clk</label>
      <radix/>
    </wave>
  </group>
  <group collapsed="false">
    <expr/>
    <label>Reset Signals</label>
    <wave>
      <expr>reset</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>top_bad_machine.reset</expr>
      <label>top_bad_machine.reset</label>
      <radix/>
    </wave>
  </group>
  <group collapsed="false">
    <expr/>
    <label>Fault Signal</label>
    <wave>
      <expr>outmem.slave_axi_cont_inmem.axi_rdata(4)</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>top_bad_machine.outmem.slave_axi_cont_inmem.axi_rdata(4)</expr>
      <label>top_bad_machine.outmem.slave_axi_cont_inmem.axi_rdata(4)</label>
      <radix/>
    </wave>
  </group>
  <group collapsed="false">
    <expr/>
    <label>FO Strobes</label>
    <wave collapsed="true">
      <expr>outmem.S_AXI_RDATA</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>top_bad_machine.outmem.S_AXI_RDATA</expr>
      <label>top_bad_machine.outmem.S_AXI_RDATA</label>
      <radix/>
    </wave>
  </group>
  <wave>
    <expr>chk_top.pb_irq</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>top_bad_machine.chk_top.pb_irq</expr>
    <label>top_bad_machine.chk_top.pb_irq</label>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.pp_irq</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>top_bad_machine.chk_top.pp_irq</expr>
    <label>top_bad_machine.chk_top.pp_irq</label>
    <radix/>
  </wave>
  <wave>
    <expr>clk</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr/>
    <label>&lt;&lt;Target&gt;&gt;::tx</label>
    <wave>
      <expr>pb_irq_i</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>reset</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <wave collapsed="true">
    <expr>subsys.main_controller.state_reg</expr>
    <label/>
    <radix>subsys.main_controller.state_reg</radix>
  </wave>
  <wave collapsed="true">
    <expr>subsys.main_controller.ext_irq</expr>
    <label/>
    <radix/>
  </wave>
  <spacer/>
  <wave collapsed="true">
    <expr>subsys.packet_builder0.M_AXI_WDATA</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.packet_builder0.fifo_in.fifo_data_s(0)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.packet_builder0.fifo_out.fifo_data_s(0)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.packet_builder0.state_reg</expr>
    <label/>
    <radix>subsys.packet_builder0.state_reg</radix>
  </wave>
  <wave collapsed="true">
    <expr>outmem.inmem_bram.ram_s(1)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>outmem.inmem_bram.ram_s(2)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>outmem.inmem_bram.ram_s(3)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>outmem.inmem_bram.ram_s(4)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.packet_builder0.axi_base_address_s</expr>
    <label/>
    <radix>subsys.packet_builder0.axi_base_address_s</radix>
  </wave>
  <wave collapsed="true">
    <expr>subsys.packet_builder0.M_AXI_AWADDR</expr>
    <label/>
    <radix/>
  </wave>
  <spacer/>
  <wave collapsed="true">
    <expr>subsys.parser.state_reg</expr>
    <label/>
    <radix>subsys.parser.state_reg</radix>
  </wave>
  <wave collapsed="true">
    <expr>subsys.parser.M_AXI_RDATA</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.parser.M_AXI_ARADDR</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>subsys.parser.pkt_ecc_uncorr_o</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>subsys.parser.pkt_ecc_corr_o</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>subsys.parser.pkt_crc_err_o</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.parser.hamming_parity_check_out_s</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>chk_top.pb_data_sel</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>top_bad_machine.chk_top.pb_data_sel</expr>
    <label>top_bad_machine.chk_top.pb_data_sel</label>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>chk_top.pb_byte_cnt</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>top_bad_machine.chk_top.pb_byte_cnt</expr>
    <label>top_bad_machine.chk_top.pb_byte_cnt</label>
    <radix/>
  </wave>
  <highlightlist>
    <!--Users can remove the highlightlist block if they want to load the signal save file into older version of JasperGold-->
    <highlight>
      <expr>subsys.parser.hamming_parity_check_out_s</expr>
      <color>builtin_red</color>
    </highlight>
  </highlightlist>
</wavelist>
