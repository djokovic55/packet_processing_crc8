<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>27</insertion-point-position>
  <wave>
    <expr>clk</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>di_debug::top.chk_top.ast_di</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.di_err</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr/>
    <label>DI_CHECKER</label>
    <wave collapsed="true">
      <expr>chk_top.di_state_reg</expr>
      <label/>
      <radix>chk_top.di_state_reg</radix>
    </wave>
    <wave collapsed="true">
      <expr>pb0_byte_cnt_top</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_top.chosen_byte</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_top.pb0_data_sel_top</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_top.chosen_byte_data</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_top.received_byte</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_top.received_byte_data</expr>
      <label/>
      <radix/>
    </wave>
    <spacer/>
    <wave collapsed="true">
      <expr>chk_top.pb_addr_in</expr>
      <label/>
      <radix/>
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
      <expr>pb_addr_out_i</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>subsys.packet_builder0.busy_o</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_top.outmem_addr_b_i</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <wave collapsed="true">
    <expr>chk_top.outmem_data_b_o</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr/>
    <label>BUILDER</label>
    <wave collapsed="true">
      <expr>subsys.packet_builder0.state_reg</expr>
      <label/>
      <radix>subsys.packet_builder0.state_reg</radix>
    </wave>
  </group>
  <wave collapsed="true">
    <expr>subsys.packet_builder0.byte_cnt_i</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>chk_top.pb0_irq_top</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.packet_builder0.fifo_in.fifo_data_s(0)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.packet_builder0.fifo_in.fifo_data_s(1)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>subsys.main_controller.state_reg</expr>
    <label/>
    <radix>subsys.main_controller.state_reg</radix>
  </wave>
  <wave collapsed="true">
    <expr>subsys.main_controller.int_irq</expr>
    <label/>
    <radix/>
  </wave>
  <highlightlist>
    <!--Users can remove the highlightlist block if they want to load the signal save file into older version of Jasper-->
    <highlight>
      <expr>chk_top.chosen_byte_data</expr>
      <color>builtin_green</color>
    </highlight>
    <highlight>
      <expr>chk_top.received_byte_data</expr>
      <color>builtin_red</color>
    </highlight>
  </highlightlist>
</wavelist>
