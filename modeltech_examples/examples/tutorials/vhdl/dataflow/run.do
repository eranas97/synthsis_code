#Copyright 1991-2016 Mentor Graphics Corporation
#
#All Rights Reserved.
#
#THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
#MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
# Simulation script for Dataflow tutorial

onbreak {resume}

# create library
if [file exists work] {
    vdel -all
}
vlib work
 
# compile all  source files
vcom -93 gates.vhd
vcom -93 v_and2.vhd util.vhd set.vhd
vcom -93 cache.vhd memory.vhd proc.vhd
vcom -93 top.vhd

# optimize design
vopt +acc top -o top_opt

# start simulator
vsim top_opt

#set WildcardFilter variables
set WildcardFilter "Variable Constant Generic Parameter SpecParam Memory Assertion Cover Endpoint ScVariable ImmediateAssert VHDLFile"

# open dataflow window
view dataflow

# wave signals
add wave /top/p/*
add log -r /*

# run simulation
run -all


