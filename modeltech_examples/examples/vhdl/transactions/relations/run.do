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

onbreak {resume}
onerror {quit -f}
onElabError {quit -f}

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Compile the source files.
vcom top.vhd

# Open the debugging windows.
quietly view *

# Simulate the design.
vsim top
run 20

# View the results.
if {![batch_mode]} {
    quietly add wave -expand top/Stream*
    quietly wave zoomfull 
    update
}

quit -f
