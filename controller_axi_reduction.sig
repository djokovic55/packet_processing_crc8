<?xml version="1.0" encoding="UTF-8"?>
<wavelist version="3">
  <insertion-point-position>42</insertion-point-position>
  <group collapsed="false">
    <expr/>
    <label>AXI</label>
    <group collapsed="false">
      <expr/>
      <label>wa_c</label>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_AWADDR</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_AWLEN</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_AWSIZE</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_AWBURST</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_AWVALID</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.axi_write_init_reg</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.master_axi_cont_ctrl.init_write_txn_pulse</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.master_axi_cont_ctrl.start_single_burst_write</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_AWREADY</expr>
        <label/>
        <radix/>
      </wave>
    </group>
    <group collapsed="false">
      <expr/>
      <label>w_c</label>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_WDATA</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_WSTRB</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_WLAST</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_WVALID</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_WREADY</expr>
        <label/>
        <radix/>
      </wave>
    </group>
    <group collapsed="true">
      <expr/>
      <label>b_c</label>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_BRESP</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_BVALID</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_BREADY</expr>
        <label/>
        <radix/>
      </wave>
    </group>
    <wave>
      <expr>system_regs.regs_cont.S_AXI_WVALID</expr>
      <label/>
      <radix/>
    </wave>
    <wave collapsed="true">
      <expr>main_controller.state_reg</expr>
      <label/>
      <radix>main_controller.state_reg</radix>
    </wave>
    <group collapsed="false">
      <expr/>
      <label>ra_c</label>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_ARADDR</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_ARLEN</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_ARSIZE</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_ARBURST</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_ARVALID</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_ARREADY</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.axi_read_init_reg</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.master_axi_cont_ctrl.init_read_txn_pulse</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.master_axi_cont_ctrl.start_single_burst_read</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>system_regs.regs_cont.S_AXI_ARVALID</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>intcon.gnt</expr>
        <label/>
        <radix/>
      </wave>
    </group>
    <group collapsed="false">
      <expr/>
      <label>r_c</label>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_RDATA</expr>
        <label/>
        <radix/>
      </wave>
      <wave collapsed="true">
        <expr>main_controller.M_AXI_RRESP</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_RLAST</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_RVALID</expr>
        <label/>
        <radix/>
      </wave>
      <wave>
        <expr>main_controller.M_AXI_RREADY</expr>
        <label/>
        <radix/>
      </wave>
    </group>
  </group>
  <wave>
    <expr>main_controller.axi_write_done_s</expr>
    <label/>
    <radix/>
  </wave>
  <wave>
    <expr>main_controller.axi_write_rdy_s</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>main_controller.regs_conf_fifo.fifo_data_s(0)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>main_controller.regs_conf_fifo.fifo_data_s(1)</expr>
    <label/>
    <radix/>
  </wave>
  <wave collapsed="true">
    <expr>main_controller.regs_conf_fifo.fifo_data_s(2)</expr>
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
      <expr>data_sel_i</expr>
      <color>builtin_blue</color>
    </highlight>
    <highlight>
      <expr>intcon.gnt</expr>
      <color>builtin_red</color>
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
    <highlight>
      <expr>chk_pb.chk_data_integrity.chosen_byte_data</expr>
      <color>#00ff00</color>
    </highlight>
    <highlight>
      <expr>chk_pb.chk_data_integrity.received_byte_data</expr>
      <color>#ff5757</color>
    </highlight>
  </highlightlist>
</wavelist>
