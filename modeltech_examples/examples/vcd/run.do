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
# Remove the "quit -f" command from this file to view the results in the GUI.
#

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Compile the sources.
vcom gates.vhd adder.vhd stimulus.vhd

# Optimize the design.
vopt testbench2 +acc -o testbench2_opt

# Create the vcd file
vsim testbench2_opt +dumpports+nocollapse
vcd dumpports -file addern.vcd /testbench2/uut/*
run 1000
quit -sim

# Re-run simulation with the vcd/stimulus file.
vsim -c -vcdstim addern.vcd addern -gn=8 
add wave /*
run 1000
quit -f
