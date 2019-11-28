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

# Compile the HDL source(s)
vlog -sv -dpiheader cimports.h simple_calls.sv cimports.c

# Simulate the design.
vsim -c top
run -all
quit -f
