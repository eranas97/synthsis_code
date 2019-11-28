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
} else {
	source $INSTALL_HOME/examples/c_posix/setup/setup_compiler_and_linker_paths_gcc.tcl
}

# Compile the HDL source(s)
vlog test.sv

# Compile the C source(s).
onerror {resume}
echo $CC -std=c99 ucdbsave.c
eval $CC -std=c99 ucdbsave.c
echo $LD ucdbsave.$ext ucdbsave.o $MTIPLILIB
eval $LD ucdbsave.$ext ucdbsave.o $MTIPLILIB

# Simulate the design and create the ucdb file.
onerror {quit -sim}
vsim -c top -pli ucdbsave.$ext
run -all
coverage save test.ucdb
vcover report -cvg -details test.ucdb

quit -f
