################################################################################
# Deadlock analysis script
################################################################################

# start with new task
task -create <dlh> -set -source_task <embedded> -copy_assumes -copy_stopats -copy_abstractions all 
# create trap assertions
check_dlh -generate -trap -inst {subsys.intcon.fsm subsys.packet_builder0 subsys.parser} -type {output fsm}
# create trap assertions on specified signals
check_dlh -generate -trap -signal {subsys.packet_builder0.state_reg subsys.parser.state_reg subsys.intcon.fsm.state_reg}
# create covers 
cover -generate -auto -instance {subsys.intcon.fsm subsys.packet_builder0 subsys.parser} -num 200 -exclude_bind_hier
