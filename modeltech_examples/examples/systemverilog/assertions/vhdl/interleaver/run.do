# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
# WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
# OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
# To run this example, bring up the simulator and type the following at the prompt:
#     do run.do
# or, to run from a shell, type the following at the shell prompt:
#     vsim -do run.do -c
# (omit the "-c" to see the GUI while running from the shell)
# Remove the "quit -f" command from this file to view the results in the GUI.
#

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work
if [file exists lib] {
    vdel -all -lib lib
}
vlib lib

# Compile the source files.
vcom -work lib -93 -cover bcest -f compile.f
vlog -work work +acc=a *.sv

# Run the first simulation with assertions.
vsim  lib.interleaver_tester interleaver_binds -L lib -assertdebug -GBUG=1 
do nofc_sim.do
quit -sim

# Run the second simulation with functional coverage.
vsim  lib.interleaver_tester interleaver_binds -L lib -GRUNFC=1 -GBUG=0 
do sim.do

quit -f
