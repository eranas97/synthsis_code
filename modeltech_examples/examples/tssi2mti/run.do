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
quietly set INSTALL_HOME [file dirname [file normalize $::env(MODEL_TECH)]]

# Set the compiler and linker paths.
if {$tcl_platform(platform) eq "windows"} {
	source $INSTALL_HOME/examples/c_windows/setup/setup_compiler_and_linker_paths_mingwgcc.tcl
} else {
	source $INSTALL_HOME/examples/c_posix/setup/setup_compiler_and_linker_paths_gcc.tcl
}

quietly regsub -all {\-ansi} $CC  "" CC
quietly regsub -all {\-pedantic} $CC "" CC

# Compile the C source(s).
echo $CC tssi2mti.c
eval $CC tssi2mti.c
echo $LD tssi2mti tssi2mti.o
eval $LD tssi2mti tssi2mti.o

# Compile the VHDL source(s).
vcom +acc top.vhd middle.vhd bottom.vhd 

# Simulate the design.
vsim -voptargs=+acc top
add list -r /*
run 100 ns
quit -sim

# Create the signals definition file
vsim -view vsim.wlf
add list -r /*
write tssi test_vectors.vec
quit -sim

# Create the stimulus file.
echo tssi2mti test_vectors.def test_vectors.vec > test_vectors.do
eval exec tssi2mti test_vectors.def test_vectors.vec > test_vectors.do

# Re-simulate using test_vectors.do
vsim -voptargs=+acc top
view list
add list -r /*
do test_vectors.do
quit -f
