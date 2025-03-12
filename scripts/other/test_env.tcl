include scripts/abstractions.tcl

clear -all

# verif
analyze -sv09 -f verif/verif.f  +define+ENV_TEST

# src
analyze -vhdl -f rtl/rtl.f

elaborate -vhdl -top {top}
clock clk
reset reset