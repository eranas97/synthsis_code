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

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Compile the HDL source(s)
vlog +cover=bcestf example.sv

# Simulate the design and create the ucdb file.
vsim -c -coverage -vopt top
transcript on
onerror { resume }
onbreak { resume }
run -all

coverage report -byinst
coverage save original.ucdb

# Delete everything but /top/dut* (ie. keep DUT)
coverage open original.ucdb
coverage edit -keeponly -path /top/dut*
coverage report -byinst
coverage save dut.ucdb

# Delete nothing but /top/dut* (ie. keep TB)
coverage open original.ucdb
coverage edit -delete -path /top/dut*
coverage report -byinst
coverage save tb.ucdb

quit -f
