#Copyright 1991-2016 Mentor Graphics Corporation
#
#All Rights Reserved.
#
#THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
#MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

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


# compile and link C source files
sccom -sc22 -suppress 6102 -I../../utils -I../basic_protocol -I../user -g main.cc
sccom -sc22 -suppress 6102 -I../../utils -I../basic_protocol -I../user -g mem_fifo_slave.cc
sccom -sc22 -suppress 6102 -I../../utils -I../basic_protocol -I../user -g ../user/master.cc  
sccom -sc22 -suppress 6102 -I../../utils -I../basic_protocol -I../user -g ../user/mem_slave.cc  
sccom -sc22 -suppress 6102 -I../../utils -I../basic_protocol -I../user -g ../user/switch_master.cc 
sccom -sc22 -link

# open debugging windows
quietly view *

# start and run simulation
vsim -sc22 toplevel
run -all 
quit -f
