vlib work

vlog test.sv -dpiheader dpi_types.h foreign.c 

vopt +acc test -o opt_test

vsim -i opt_test -do "view source"
