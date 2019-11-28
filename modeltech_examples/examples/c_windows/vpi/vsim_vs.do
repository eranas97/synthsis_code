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
echo $CC vpi_test.c
eval exec $CC vpi_test.c 2>@ stdout
echo $LD -export:vlog_startup_routines vpi_test.obj
eval $LD -export:vlog_startup_routines vpi_test.obj

# Compile the Verilog source(s).
vlog prim.v dff.v top.v

# Simulate the design.
vsim top -pli vpi_test.dll
run -all
quit -f
