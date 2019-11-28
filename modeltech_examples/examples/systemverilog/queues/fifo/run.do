#
# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
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
vlog -sv +define+ASSERT fifo.v fifo_tb.v

# Simulate the design.
vsim -voptargs=+acc=r fifo_tb

# View the results.
if {![batch_mode]} {
	log -r *
	add wave -divider "Testbench Signals"
	add wave /fifo_tb/clock
	add wave /fifo_tb/nReset
	add wave /fifo_tb/nWrite
	add wave /fifo_tb/nRead
	add wave -hex /fifo_tb/data
	add wave -divider "DUT Outputs"
	add wave /fifo_tb/empty
	add wave /fifo_tb/full
	add wave -hex /fifo_tb/q
	wave zoomfull
}
run -all

quit -f

