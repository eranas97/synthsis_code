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

# Compile the C source(s)
echo $CC vpi_test.c
eval $CC vpi_test.c 
echo $LD vpi_test.dll vpi_test.o $MTIPLILIB
eval $LD vpi_test.dll vpi_test.o $MTIPLILIB

# Compile the Verilog source(s).
vlog prim.v dff.v top.v

# Simulate the design.
vsim -c -do vsim.do top -pli vpi_test.dll
run -all
quit -f
