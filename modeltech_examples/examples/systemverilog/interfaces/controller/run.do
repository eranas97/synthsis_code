#
# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
# PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
# LICENSE TERMS.
#
# To run this example, bring up the simulator and type the following at the prompt:
#     do run.do
# or, to run from a shell, type the following at the shell prompt:
#     vsim -c -do run.do
# (omit the "-c" to see the GUI while running from the shell)
# Remove the "quit -f" command from this file to view the results in the GUI.
#

onbreak {resume}

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Compile the sources.
vlog -sv +define+ASSERT memory.v control.v mem_if.v testbench.v

# Simulate the design.
vsim testbench
run -all

# View the results.
if {![batch_mode]} {
	log -r /*
	add wave -divider "Testbench Signals"
	add wave /testbench/clock
	add wave /testbench/start
	add wave -divider "Interface Signals"
	add wave -hex /testbench/I0/DATA
	add wave -hex /testbench/I0/ADDR
	add wave /testbench/I0/MRD
	add wave /testbench/I0/MWR
	add wave -divider "Memory"
	add wave -hex /testbench/I2/MEM
	add wave -divider "Controller"
	add wave -hex /testbench/I1/IR
	add wave -hex /testbench/I1/regC
	wave zoomfull
}

quit -f
