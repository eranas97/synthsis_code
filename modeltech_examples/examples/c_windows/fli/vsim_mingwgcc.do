# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
# WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
# OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

# Use this vsim_mingwgcc.do file to run this example.
# Either bring up ModelSim and type the following at the "ModelSim>" prompt:
#     do vsim_mingwgcc.do
# or, to run from a shell, type the following at the shell prompt:
#     vsim -do vsim_mingwgcc.do -c
# (omit the "-c" to see the GUI while running from the shell)

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Get the simulator installation directory.
quietly set INSTALL_HOME [file dirname [file nativename $::env(MODEL_TECH)]]

# Set the compiler and linker paths.
source $INSTALL_HOME/examples/c_windows/setup/setup_compiler_and_linker_paths_mingwgcc.tcl

# Compile the C source(s).
echo $CC dumpdes.c gates.c monitor.c
eval $CC dumpdes.c gates.c monitor.c
echo $LD dumpdes.so dumpdes.o $MTIPLILIB
eval $LD dumpdes.so dumpdes.o $MTIPLILIB
echo $LD gates.so gates.o $MTIPLILIB
eval $LD gates.so gates.o $MTIPLILIB
echo $LD monitor.so monitor.o $MTIPLILIB
eval $LD monitor.so monitor.o $MTIPLILIB

# Compile the VHDL source(s).
vcom foreign.vhd

# Simulate the design.
vsim testbench
onerror {resume}
view structure
view signals
add wave *
run 500
quit -f
