#
# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# To run this example, bring up the simulator and type the following at the prompt:
#     do run.do
# or, to run from a shell, type the following at the shell prompt:
#     vsim -do run.do -c
# (omit the "-c" to see the GUI while running from the shell)
#

onbreak {resume}

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Compile the sources.
vlog -sv mux_ff.v gcd.v top.v tb.v

# Optimize the design using -xprop (default mode is "resolve").
vopt tb +acc -xprop -o tbout

# Simulate the optimized design.
vsim tbout

# View the results.
if {![batch_mode]} {
	log -r *
	add wave /tb/T1/XPROP_COMB_47
	add wave /tb/T1/XPROP_COMB_72
	add wave /tb/T1/state
	add wave /tb/T1/state_pf/XPROP_FF_34
	add wave /tb/T1/state_pf/reset
	add wave /tb/T1/G1/A_mux/XPROP_COMB_54
	add wave /tb/T1/G1/A_mux/XPROP_COMB_56
	add wave /tb/T1/G1/A_mux/XPROP_COMB_58
	add wave /tb/T1/G1/A_mux/select
	add wave /tb/T1/G1/B_mux/XPROP_COMB_75
	add wave /tb/T1/G1/B_mux/select
	add wave /tb/T1/G1/A_f/XPROP_FF_22
	add wave /tb/T1/G1/A_f/en_p
	add wave /tb/T1/G1/B_f/XPROP_FF_22
	add wave /tb/T1/G1/B_f/en_p
	wave zoomfull
}
run -all

if {[batch_mode]} {
quit -f
}
