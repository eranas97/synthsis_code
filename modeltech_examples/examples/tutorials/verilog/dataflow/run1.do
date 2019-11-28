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
vlog gates.v and2.v cache.v memory.v proc.v set.v top.v

# start simulator
vsim top

#set WildcardFilter variables
set WildcardFilter "Variable Constant Generic Parameter SpecParam Memory Assertion Cover Endpoint ScVariable ImmediateAssert VHDLFile"

# wave signals
add wave /top/p/*
add log -r /*

# run simulation
run -all

