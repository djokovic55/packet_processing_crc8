main:
	jg do.tcl

int:
	jg do_int.tcl

top:
	jg do_top.tcl

pb:
	jg do_pb.tcl

pp:
	jg do_pp.tcl

.PHONY: clean
clean:
	rm -rf jgproject
