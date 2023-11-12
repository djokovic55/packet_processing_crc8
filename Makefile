main:
	jg do.tcl

int_w_cont:
	jg do_intcon_w_controllers.tcl

phase2:
	jg do_phase2.tcl

pb:
	jg do_pb.tcl

pp:
	jg do_pp.tcl

.PHONY: clean
clean:
	rm -rf jgproject
