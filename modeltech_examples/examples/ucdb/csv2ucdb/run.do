#
# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
# WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
# OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
#
# To run this example, bring up the simulator and type the following at the prompt:
#     do run.do
# or, to run from a shell, type the following at the shell prompt:
#     vsim -c -do run.do
# (omit the "-c" to see the GUI while running from the shell)
#

onerror {resume}
# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Get the simulator installation directory.
quietly set INSTALL_HOME [ file dirname [file normalize $::env(MODEL_TECH)]]

# Set the compiler and linker paths.
if {$tcl_platform(platform) eq "windows"} {
	source $INSTALL_HOME/examples/c_windows/setup/setup_compiler_and_linker_paths_mingwgcc.tcl
	if {$is64bit == 1 } {
		quietly set RESFILE csv2ucdb64.res
	} else {
		quietly set RESFILE csv2ucdb32.res
	}
	quietly set ADDL_DEFINES -DWIN32
} else {
	source $INSTALL_HOME/examples/c_posix/setup/setup_compiler_and_linker_paths_gcc.tcl
	quietly set RESFILE ""
	quietly set ADDL_DEFINES ""
}

# Compile the C source(s)
quietly set LD $UCDB_LD
if {$platform eq "sunos5v9"} {
	echo $CC csv2ucdb.c $ADDL_DEFINES
	eval $CC csv2ucdb.c $ADDL_DEFINES
} else {
	echo $CC -std=c99 csv2ucdb.c $ADDL_DEFINES
	eval $CC -std=c99 csv2ucdb.c $ADDL_DEFINES
}
echo $LD csv2ucdb csv2ucdb.o $UCDBLIB $RESFILE
eval $LD csv2ucdb csv2ucdb.o $UCDBLIB $RESFILE

# Compile the HDL source(s)
vlog simple.sv

# Simulate 4 different times to get different coverage per test:
onerror {quit -sim}
vsim -c top -vopt -sv_seed 1 -GNUMCLOCKS=50 
set test simple1; do simple.do

vsim -c top -vopt -sv_seed 2 -GNUMCLOCKS=50
set test simple2; do simple.do

vsim -c top -vopt -sv_seed 3 -GNUMCLOCKS=50 
set test simple3; do simple.do

vsim -c top -vopt -sv_seed 4 -GNUMCLOCKS=0 
set test simple4; do simple.do

# Call the test plan converter, does the merge, and analysis.
vsim -c
do simple_merge.do

quit -f
