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
		quietly set RESFILE dayinthelife64.res
	} else {
		quietly set RESFILE dayinthelife32.res
	}
} else {
	source $INSTALL_HOME/examples/c_posix/setup/setup_compiler_and_linker_paths_gcc.tcl
	quietly set RESFILE ""
}

# Compile the C source(s).
quietly set LD $UCDB_LD
if {$platform eq "sunos5v9"} {
	echo $CC dayinthelife.c
	eval $CC dayinthelife.c
} else {
	echo $CC -std=c99 dayinthelife.c
	eval $CC -std=c99 dayinthelife.c
}
echo $LD dayinthelife dayinthelife.o $UCDBLIB $RESFILE
eval $LD dayinthelife dayinthelife.o $UCDBLIB $RESFILE

# Run the UCDB application.
echo dayinthelife
dayinthelife

quit -f
