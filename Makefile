main:
	jg do.tcl

int_w_cont:
	jg do_intcon_w_controllers.tcl

.PHONY: clean
clean:
	rm -rf jgproject
