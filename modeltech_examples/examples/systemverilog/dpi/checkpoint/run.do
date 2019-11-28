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
#     do run.do
# or, to run from a shell, type the following at the shell prompt:
#     vsim -c -do run.do
# (omit the "-c" to see the GUI while running from the shell)
#

onerror {resume}
# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Compile the HDL source(s)
vlog -sv -dpiheader cimports.h checkpoint.sv cimports.c

# Simulate the design.
onerror {quit -sim}
vsim -c top
onbreak {resume}
transcript on
run 100
checkpoint checkpt100.dat
# warm restore run
restore checkpt100.dat
echo $now
quit -sim
# cold restore run
vsim -restore checkpt100.dat
quit -sim
quit -f
