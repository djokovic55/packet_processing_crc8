<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>21</insertion-point-position>
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
  <wave collapsed="true">
    <expr>subsys.parser.M_AXI_RDATA</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>top_bad_machine.subsys.parser.M_AXI_RDATA</expr>
    <label>top_bad_machine.subsys.parser.M_AXI_RDATA</label>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr/>
    <label>FO Strobes</label>
    <wave collapsed="true">
      <expr>subsys.parser.header_reg</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>top_bad_machine.subsys.parser.header_reg</expr>
      <label>top_bad_machine.subsys.parser.header_reg</label>
      <radix/>
    </wave>
  </group>
  <wave collapsed="true">
    <expr>subsys.parser.hamming_parity_check_out_s</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>top_bad_machine.subsys.parser.hamming_parity_check_out_s</expr>
    <label>top_bad_machine.subsys.parser.hamming_parity_check_out_s</label>
    <radix/>
  </wave>
  <wave>
    <expr>subsys.parser.hamming_msb_parity_bit_s</expr>
    <label>subsys.parser.hamming_msb_parity_bit_s</label>
    <radix/>
  </wave>
  <wave>
    <expr>top_bad_machine.subsys.parser.hamming_msb_parity_bit_s</expr>
    <label/>
    <radix/>
  </wave>
  <spacer/>
  <wave collapsed="true">
    <expr>subsys.parser.pkt_byte_cnt_o_reg</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>top_bad_machine.subsys.parser.pkt_byte_cnt_o_reg</expr>
    <label>top_bad_machine.subsys.parser.pkt_byte_cnt_o_reg</label>
    <radix/>
  </wave>
  <wave>
    <expr>subsys.parser.pkt_ecc_corr_o</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>top_bad_machine.subsys.parser.pkt_ecc_corr_o</expr>
    <label>top_bad_machine.subsys.parser.pkt_ecc_corr_o</label>
    <radix/>
  </wave>
  <wave>
    <expr>subsys.parser.pkt_ecc_uncorr_o</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>top_bad_machine.subsys.parser.pkt_ecc_uncorr_o</expr>
    <label>top_bad_machine.subsys.parser.pkt_ecc_uncorr_o</label>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.parser.state_reg</expr>
    <label/>
    <radix>subsys.parser.state_reg</radix>
  </wave>
  <wave collapsed="true">
    <expr>top_bad_machine.subsys.parser.state_reg</expr>
    <label>top_bad_machine.subsys.parser.state_reg</label>
    <radix>top_bad_machine.subsys.parser.state_reg</radix>
  </wave>
</wavelist>
