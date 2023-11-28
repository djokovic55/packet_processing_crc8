<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>9</insertion-point-position>
  <wave>
    <expr>clk</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr>&lt;&lt;Target&gt;&gt;::tx</expr>
    <label>&lt;&lt;Target&gt;&gt;::tx</label>
    <wave>
      <expr>packet_builder0.chk_data_integrity.reset</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>packet_builder0.chk_data_integrity.chosen_packet_arrived</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <wave collapsed="true">
    <expr>packet_builder0.chk_data_integrity.chosen_byte</expr>
    <label/>
    <radix>hex</radix>
  </wave>
  <wave collapsed="true">
    <expr>packet_builder0.chk_data_integrity.chosen_byte_data</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>packet_builder0.chk_data_integrity.received_byte</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>packet_builder0.chk_data_integrity.received_byte_data</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>packet_builder0.state_reg</expr>
    <label/>
    <radix>packet_builder0.state_reg</radix>
  </wave>
</wavelist>
