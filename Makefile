main:
	jg ./scripts/do_top.tcl &

.PHONY: clean
clean:
	rm -rf jgproject
