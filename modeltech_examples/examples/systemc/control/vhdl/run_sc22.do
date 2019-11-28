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
#     vsim -do run.do -c
# (omit the "-c" to see the GUI while running from the shell)

onbreak {resume}

# create library
if [file exists work] {
    vdel -all
}
vlib work

# compile the VHDL source files
vcom -93 *.vhd

# generate foreign module declaration
scgenmod ringbuf > ringbuf.h

# compile and link C source files
sccom -sc22 -g test_ringbuf.cpp
sccom -sc22 -link

# open debugging windows
quietly view *

# start and run simulation
vsim -sc22 test_ringbuf
set StdArithNoWarnings 1
run 1000 ns
