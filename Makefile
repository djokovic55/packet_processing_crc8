main:
	jg ./scripts/do_top.tcl &

test_env:
	jg ./scripts/other/test_env.tcl &

.PHONY: clean
clean:
	rm -rf jgproject
