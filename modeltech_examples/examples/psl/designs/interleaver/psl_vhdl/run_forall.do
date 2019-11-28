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

# Compile the source files.
vcom -93 -f compile_forall.f

# Run the first simulation.
vsim interleaver_tester -nopsl 
set StdArithNoWarnings 1
onbreak {resume}
run -all
quit -sim

# Run the second simulation with assertions.
vsim interleaver_tester -assertdebug -GBUG=1 -do "do nofc_forall_sim.do"
# do nofc_forall_sim.do
quit -sim

# Run the third simulation with functional coverage.
vsim interleaver_tester -GRUNFC=1 -GBUG=0 
do forall_sim.do 
run 70 us

quit -f
