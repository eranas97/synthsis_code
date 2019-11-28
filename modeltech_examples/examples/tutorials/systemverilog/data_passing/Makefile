worklib:
	vlib work

compile:  test.sv foreign.c
	vlog test.sv -dpiheader dpi_types.h  foreign.c

optimize:
	vopt +acc test -o opt_test

sim:
	vsim opt_test

all: worklib compile optimize sim

clean:
	rm -rf work transcript vsim.wlf dpi_types.h
