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

# Compile the source files.
vlog dram.v
vlog +define+BUG=1 dramcon_rtl.sv -pslfile dram_cntrl.psl
vlog dramcon_sim.v -pslfile dram_tb.psl
vopt +acc tb -o dram_opt

# Run the first simulation without psl.
vsim -nopsl dram_opt
onbreak {resume}
run -all
