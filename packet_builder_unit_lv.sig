<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>15</insertion-point-position>
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
    <wave>
      <expr>chk_pb.axi_arv_arr_flag</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>master_axi_cont_ctrl.init_read_txn_pulse</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>master_axi_cont_ctrl.start_single_burst_read</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>master_axi_cont_ctrl.burst_read_active</expr>
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
  <group collapsed="true">
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
    <wave collapsed="true">
      <expr>fifo_out_wr_data_reg</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>crc_reg</expr>
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
  <group collapsed="true">
    <expr/>
    <label>AXI_WRITE</label>
    <wave collapsed="true">
      <expr>M_AXI_AWADDR</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>M_AXI_AWLEN</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>M_AXI_AWSIZE</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>M_AXI_AWBURST</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>M_AXI_AWVALID</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>chk_pb.awready</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>chk_pb.axi_awv_awr_flag</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>master_axi_cont_ctrl.init_write_txn_pulse</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>master_axi_cont_ctrl.start_single_burst_write</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>master_axi_cont_ctrl.burst_write_active</expr>
      <label/>
      <radix/>
    </wave>
    <spacer/>
    <wave collapsed="true">
      <expr>M_AXI_WDATA</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>M_AXI_WSTRB</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>master_axi_cont_ctrl.axi_wlast</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>M_AXI_WVALID</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>chk_pb.wready</expr>
      <label/>
      <radix/>
    </wave>
    <spacer/>
    <wave collapsed="true">
      <expr>chk_pb.bresp</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>chk_pb.bvalid</expr>
      <label/>
      <radix/>
    </wave>
    <wave>
      <expr>M_AXI_BREADY</expr>
      <label/>
      <radix/>
    </wave>
    <highlightlist>
      <!--Users can remove the highlightlist block if they want to load the signal save file into older version of JasperGold-->
      <highlight>
        <expr>FIFO_IN</expr>
        <color>builtin_blue</color>
      </highlight>
      <highlight>
        <expr>M_AXI_ARADDR</expr>
        <color>builtin_red</color>
      </highlight>
      <highlight>
        <expr>M_AXI_ARREADY</expr>
        <color>builtin_green</color>
      </highlight>
      <highlight>
        <expr>M_AXI_ARVALID</expr>
        <color>builtin_red</color>
      </highlight>
      <highlight>
        <expr>M_AXI_AWADDR</expr>
        <color>builtin_red</color>
      </highlight>
      <highlight>
        <expr>M_AXI_AWVALID</expr>
        <color>builtin_red</color>
      </highlight>
      <highlight>
        <expr>M_AXI_BREADY</expr>
        <color>builtin_red</color>
      </highlight>
      <highlight>
        <expr>M_AXI_RDATA</expr>
        <color>builtin_green</color>
      </highlight>
      <highlight>
        <expr>M_AXI_RREADY</expr>
        <color>builtin_red</color>
      </highlight>
      <highlight>
        <expr>M_AXI_RRESP</expr>
        <color>builtin_green</color>
      </highlight>
      <highlight>
        <expr>M_AXI_WDATA</expr>
        <color>builtin_red</color>
      </highlight>
      <highlight>
        <expr>M_AXI_WSTRB</expr>
        <color>builtin_red</color>
      </highlight>
      <highlight>
        <expr>M_AXI_WVALID</expr>
        <color>builtin_red</color>
      </highlight>
      <highlight>
        <expr>chk_pb.awready</expr>
        <color>builtin_green</color>
      </highlight>
      <highlight>
        <expr>chk_pb.axi_awv_awr_flag</expr>
        <color>builtin_green</color>
      </highlight>
      <highlight>
        <expr>chk_pb.bresp</expr>
        <color>builtin_green</color>
      </highlight>
      <highlight>
        <expr>chk_pb.bvalid</expr>
        <color>builtin_green</color>
      </highlight>
      <highlight>
        <expr>chk_pb.rlast</expr>
        <color>builtin_green</color>
      </highlight>
      <highlight>
        <expr>chk_pb.rvalid</expr>
        <color>builtin_green</color>
      </highlight>
      <highlight>
        <expr>chk_pb.wready</expr>
        <color>builtin_green</color>
      </highlight>
      <highlight>
        <expr>master_axi_cont_ctrl.axi_wlast</expr>
        <color>builtin_red</color>
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
  </group>
</wavelist>
