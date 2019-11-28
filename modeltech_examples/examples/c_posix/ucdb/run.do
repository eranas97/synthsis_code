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

# Set compiler and linker paths.
source $INSTALL_HOME/examples/c_posix/setup/setup_compiler_and_linker_paths_gcc.tcl

# Compile the HDL source(s)
vlog -fsmverbose -cover bsectf -sv test.v
vcom -fsmverbose -cover bsectf test.vhd

# Simulate the design and create the ucdb file.
vsim -togglenovlogints -coverage -c top
onbreak resume;
run -all; 
coverage attr -comment "UCDB example with many kinds of coverage"
coverage save test.ucdb
quit -sim

# Compile the C source(s).
onerror {resume}
quietly set LD $UCDB_LD
if {$platform eq "sunos5v9"} {
	echo $CC ucdbdump.c
	eval $CC ucdbdump.c
} else {
	echo $CC -std=c99 ucdbdump.c
	eval $CC -std=c99 ucdbdump.c
}
echo $LD ucdbdump ucdbdump.o $UCDBLIB
eval $LD ucdbdump ucdbdump.o $UCDBLIB

# Run the UCDB application.
echo ucdbdump test.ucdb -o test.dump
eval exec ucdbdump test.ucdb -o test.dump
quit -f
