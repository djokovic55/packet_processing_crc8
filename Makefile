
test_env:
	jg ./scripts/other/test_env.tcl &

main:
	jg ./scripts/do_top.tcl &

.PHONY: clean
clean:
	rm -rf jgproject
