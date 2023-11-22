main:
	jg do.tcl

int:
	jg do_int.tcl

phase2:
	jg do_phase2.tcl

pb:
	jg do_pb.tcl

pp:
	jg do_pp.tcl

.PHONY: clean
clean:
	rm -rf jgproject
