# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
# WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
# OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
#
# To run this example, bring up the simulator and type the following at the prompt:
#     do run_nopsl.do
# or, to run from a shell, type the following at the shell prompt:
#     vsim -do run_nopsl.do -c
# (omit the "-c" to see the GUI while running from the shell)
#

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Compile the source files with psl.
vlog test.v -pslfile test.psl

# Run the first simulation with psl.
vsim work.tb -l results/transcript1
onbreak {resume}
run 1000

# Run the second simulation without psl.
vsim -nopsl work.tb -l results/transcript2
onbreak {resume}
run 1000

# Compile the source files with -nopsl switch.
vlog -nopsl test.v -pslfile test.psl

# Run the third simulation with psl.
vsim work.tb -l results/transcript3
onbreak {resume}
run 1000

# Run the fourth simulation without psl.
vsim -nopsl work.tb -l results/transcript4
onbreak {resume}
run 1000

quit -f

