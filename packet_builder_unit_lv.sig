<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>36</insertion-point-position>
  <wave>
    <expr>M_AXI_ACLK</expr>
    <label/>
    <radix/>
  </wave>
  <group collapsed="false">
    <expr>&lt;&lt;Target&gt;&gt;::tx</expr>
    <label>&lt;&lt;Target&gt;&gt;::tx</label>
    <wave>
      <expr>start_i</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>M_AXI_ARESETN</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <wave collapsed="true">
    <expr>state_reg</expr>
    <label/>
    <radix>state_reg</radix>
  </wave>
  <group collapsed="true">
    <expr/>
    <label>AXI_READ</label>
    <wave collapsed="true">
      <expr>M_AXI_ARADDR</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>M_AXI_ARLEN</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_pb.arlen</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>M_AXI_ARSIZE</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>M_AXI_ARBURST</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>M_AXI_ARVALID</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>M_AXI_ARREADY</expr>
      <label/>
      <radix/>
    </wave>
    <spacer/>
    <wave collapsed="true">
      <expr>M_AXI_RDATA</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>chk_pb.rlast</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>chk_pb.arlen_cntr</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>chk_pb.rnext</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>chk_pb.rvalid</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>M_AXI_RREADY</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>M_AXI_RRESP</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <spacer/>
  <group collapsed="true">
    <expr/>
    <label>CRC_CALC</label>
    <wave collapsed="true">
      <expr>crc_calc.state_reg</expr>
      <label/>
      <radix>crc_calc.state_reg</radix>
    </wave>
    <wave collapsed="true">
      <expr>crc_calc.data_in</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>crc_calc.crc_data_in_s</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>crc_calc.data_req</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>crc_calc.crc_reg</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>crc_calc.crc_calc.data_in</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>crc_calc.crc_calc.crc_in</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>crc_calc.crc_calc.crc_out</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>crc_calc.crc_ready</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <spacer/>
  <group collapsed="false">
    <expr/>
    <label>FIFO_IN</label>
    <group collapsed="false">
      <expr/>
      <label>FIFO_IN_DATA</label>
      <wave collapsed="true">
        <expr>fifo_in.fifo_data_s(0)</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>fifo_in.fifo_data_s(1)</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>fifo_in.fifo_data_s(2)</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>fifo_in.fifo_data_s(3)</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>fifo_in.fifo_data_s(4)</expr>
        <label/>
        <radix/>
      </wave>
    </group>
    <wave collapsed="true">
      <expr>fifo_in_wr_data_s</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>axi_read_data_s</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>fifo_in.read_index_s</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>fifo_in.write_index_s</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>fifo_in_rd_data_s</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <spacer/>
  <group collapsed="false">
    <expr/>
    <label>BUILDER</label>
    <wave collapsed="true">
      <expr>state_reg</expr>
      <label/>
      <radix>state_reg</radix>
    </wave>
    <wave collapsed="true">
      <expr>header_s</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>written_pulse_bytes_reg</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>pulse_cnt_reg</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>write_burst_len_reg</expr>
      <label/>
      <radix/>
    </wave>
  </group>
  <group collapsed="false">
    <expr/>
    <label>FIFO_OUT</label>
    <wave>
      <expr>fifo_out.wr_en_i</expr>
      <label/>
      <radix/>
    </wave>
    <group collapsed="false">
      <expr/>
      <label>FIFO_DATA_OUT</label>
      <wave collapsed="true">
        <expr>fifo_out.fifo_data_s(0)</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>fifo_out.fifo_data_s(1)</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>fifo_out.fifo_data_s(2)</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>fifo_out.fifo_data_s(3)</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>fifo_out.fifo_data_s(4)</expr>
        <label/>
        <radix/>
      </wave>
    </group>
  </group>
  <spacer/>
  <highlightlist>
    <!--Users can remove the highlightlist block if they want to load the signal save file into older version of JasperGold-->
    <highlight>
      <expr>FIFO_IN</expr>
      <color>builtin_blue</color>
    </highlight>
    <highlight>
      <expr>state_reg</expr>
      <color>builtin_red</color>
    </highlight>
    <highlight>
      <expr>written_pulse_bytes_reg</expr>
      <color>builtin_orange</color>
    </highlight>
  </highlightlist>
</wavelist>
