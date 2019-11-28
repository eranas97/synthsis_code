# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
# WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
# OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

# Use this run.do file to run this example.
# Either bring up ModelSim and type the following at the "ModelSim>" prompt:
#     do run.do
# or, to run from a shell, type the following at the shell prompt:
#     vsim -sc22 -do run.do -c
# (omit the "-c" to see the GUI while running from the shell)

onbreak {resume}

# create library
if [file exists work] {
    vdel -all
}
vlib work

#compile SystemVerilog source file
vlog hello.sv

# compile and link C source files
sccom -sc22 -g -DMTI_BIND_SC_MEMBER_FUNCTION hello.cpp
sccom -sc22 -link

# start and run simulation
vsim -sc22 hello_top hello_sc_top

run -all
quit -f 
