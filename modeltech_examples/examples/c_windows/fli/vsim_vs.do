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
#     do vsim_vs.do
# or, to run from a shell, type the following at the shell prompt:
#     vsim -c -do vsim_vs.do
# (omit the "-c" to see the GUI while running from the shell)
#

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Get the simulator installation directory.
quietly set INSTALL_HOME [file dirname [file nativename $::env(MODEL_TECH)]]

# Set the compiler and linker paths.
source $INSTALL_HOME/examples/c_windows/setup/setup_compiler_and_linker_paths_vs.tcl

# Compile the C source(s)
echo $CC dumpdes.c gates.c monitor.c
eval exec $CC dumpdes.c gates.c monitor.c 2>@ stdout
echo $LD -export:dump_design_init dumpdes.obj /out:dumpdes.so
eval $LD -export:dump_design_init dumpdes.obj /out:dumpdes.so
echo $LD -export:and_gate_init gates.obj /out:gates.so
eval $LD -export:and_gate_init gates.obj /out:gates.so
echo $LD -export:monitor_init monitor.obj /out:monitor.so
eval $LD -export:monitor_init monitor.obj /out:monitor.so

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
