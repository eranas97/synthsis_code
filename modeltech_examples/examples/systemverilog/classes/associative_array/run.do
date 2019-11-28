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
#

onbreak {resume}
onerror {quit -f}

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Compile first design.
vlog assoc.sv

# Simulate first design.
vsim -c top
run -all
quit -sim

# Compile second design.
vlog +define+FIELD assoc.sv

# Simulate second design.
vsim -c top
run -all
quit -f
