worklib:
	vlib work

compile:  test.sv
	vlog test.sv -dpiheader dpi_types.h

foreign:  foreign.c
	gcc -I$(QUESTA_HOME)/include -shared -fPIC -g -o foreign.so foreign.c

foreign_32:  foreign.c
	gcc -I$(QUESTA_HOME)/include -shared -fPIC -m32 -g -o foreign.so foreign.c

optimize:
	vopt +acc test -o opt_test

foreign_windows:  foreign.c
	vsim -c opt_test -dpiexportobj exports
	gcc -I$(QUESTA_HOME)/include -shared -g -o foreign.dll foreign.c exports.obj -lmtipli -L$(QUESTA_HOME)/win32

sim:
	vsim opt_test -sv_lib foreign

all: worklib compile foreign optimize sim

all_32: worklib compile foreign_32 optimize sim

all_windows: worklib compile optimize foreign_windows sim

clean:
	rm -rf work transcript vsim.wlf foreign.so foreign.dll exports.obj

