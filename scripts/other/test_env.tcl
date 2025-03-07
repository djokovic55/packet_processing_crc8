clear -all

# verif
# analyze -sv09 -f verif/interfaces/pb_conf_port_intf.sv
analyze -sv09 verif/fv_adapter.sv verif/pp_env_pkg.sv
analyze -sv09 -f verif/verif.f  +define+ENV_TEST
# analyze -sv09 -f /verif/inmem_port_b_intf.sv
# analyze -sv09 -f /verif/outmem_port_b_intf.sv
# analyze -sv09 -f /verif/pb_conf_port_intf.sv
# analyze -sv09 -f /verif/pp_conf_port_intf.sv
# analyze -sv09 -f /verif/regs_port_intf.sv


# src
analyze -vhdl -f rtl/rtl.f

elaborate -vhdl -top {top}
clock clk
reset reset