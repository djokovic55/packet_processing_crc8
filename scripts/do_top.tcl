clear -all

# Include path is relative to the repo root directory (packet_processing_crc8)
include scripts/sst/ps_pb0_di.tcl
include scripts/sst/sst_pb0_di.tcl
include scripts/abstractions.tcl
include scripts/coverage.tcl
################################################################################
# Init coverage app 
################################################################################
check_cov -init
set_prove_time_limit 0s
# check_cov -init -type {proof bound} -model all -exclude_instance { * } -include_instance {subsys.chk_data_integrity} 
# check_cov -init -type {bound}
################################################################################

################################################################################
# Init fsv app 
################################################################################
# check_fsv -init
################################################################################

# set_proof_structure_support_embedded_on_case_split on

################################################################################
# Elaboration
################################################################################
# verif

analyze -sv09 -f verif/verif.f +define+SST
# src
analyze -vhdl -f rtl/rtl.f

elaborate -vhdl -top {top}
clock clk
reset reset

################################################################################
## CALL ABSTRACTIONS
################################################################################
# registers_iva_abs_proc
# blackbox_controller_abs_proc
# inmem_iva_abs_proc
# disable_pb1_proc

################################################################################
# CHECK FOR CONFLICTS, ENABLE DEAD_END PROP
################################################################################
check_assumptions -show -dead_end
# task -create dead_end -set -source_task iva_debug -copy_stopats -copy_ratings -copy_abstractions all -copy_assumes -copy iva_debug:::noDeadEnd

################################################################################
## CALL SCRIPTS
################################################################################
# script for further SST helper development from scripts/sst/sst_pb0_di.tcl
	# run_sst_pb0_proc
# script to see helper proof structure from scripts/sst/ps_pb0_di.tcl
	# run_proof_structure_proc
# script for coverage analysis from scripts/coverage.tcl
	# run_coverage_proc

################################################################################
# Formal Profiler
################################################################################
# formal_profiler -property <prop> -viewer
# get_design_info -property <embedded>::top.chk_top.ast_pb0_di_coverage -gui

################################################################################
## PROVE with differrent engine
################################################################################
# Inititiate using M engine
# prove -task crc_debug -engine_mode {M} -bg
################################################################################

################################################################################
## DEEP BUG HUNTING
################################################################################
# prove the existing trace as initial value for another formal proof.

# prove -from iva_debug::top.chk_top.cov_2pb0 -task . -bg
################################################################################

################################################################################
# START COVERAGE ANALYSIS
################################################################################
# check_cov -measure -task {<embedded>} -bg

################################################################################
# FORMAL SAFETY APP COMMANDS
################################################################################
#
# check_fsv -fault -add subsys.parser.axi_read_data_s(4) -type SA1 -silent
# ADD FAULTS
# check_fsv -fault -add outmem.slave_axi_cont_inmem.axi_rdata(4) -type SA1 -silent
# ADD STROBES
# check_fsv -strobe -add outmem.S_AXI_RDATA -functional
# check_fsv -strobe -add subsys.parser.header_reg -functional
# check_fsv -strobe -add subsys.parser.hamming_parity_check_out_s -checker -checker_mode diff
# set_fsv_generate_detectability On; set_fsv_clock_cycle_time 0
# set_fsv_generate_always_propagated On; set_fsv_generate_always_detected On; set_fsv_clock_cycle_time 0
# check_fsv -structural
# check_fsv -generate
# check_fsv -prove

## Use the existing trace as initial value for another formal proof.
#prove -from <embedded>::top.chk_top.cov_no_ecc_uncorr_err -task . -bg
