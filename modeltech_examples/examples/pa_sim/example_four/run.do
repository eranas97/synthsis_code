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
#     vsim -do run.do -c
# (omit the "-c" to see the GUI while running from the shell)

onbreak {resume}
#if {[batch_mode]} {
#    echo "Run this test in the GUI mode."
#    quit -f
#}

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Compile the source files.
vlog -work work -f compile_rtl.f

# Optimize the design.
 vopt -work work +acc -pa_enable=highlight+debug \
     rtl_top \
     interleaver_tester \
     -pa_upf rtl_top.upf \
     -pa_top "/interleaver_tester/dut" \
     -pa_genrpt=pa+de+v+u \
     -pa_checks=s+ul+i+r+p+cp+upc+ugc -pa_coverage=state\
     -o top_opt

# Simulate the design and view the results.
vsim top_opt \
     -vopt_verbose \
     +nowarnTSCALE \
     +nowarnTFMPC \
     -l rtl.log \
     -wlf rtl.wlf \
     -pa \
     -pa_highlight \
     -coverage \
     +notimingchecks \
     -msgmode both \
     -displaymsgmode both \
     -voptargs=+acc

log -r /*
if {![batch_mode]} {
add wave -expand -group "Testbench Signals"
add wave -group "Testbench Signals" /interleaver_tester/clock1
add wave -group "Testbench Signals" /interleaver_tester/clock2
add wave -group "Testbench Signals" /interleaver_tester/reset_n
add wave -expand -group "Power Control Signals"
add wave -group "Power Control Signals" /interleaver_tester/mc_PWR
add wave -group "Power Control Signals" /interleaver_tester/mc_SAVE
add wave -group "Power Control Signals" /interleaver_tester/mc_RESTORE
add wave -group "Power Control Signals" /interleaver_tester/mc_ISO
add wave -group "Power Control Signals" /interleaver_tester/mc_CLK_GATE
add wave -group "Power Control Signals" /interleaver_tester/sram_PWR
add wave -group "Interleaver"
add wave -group "Interleaver" -ports /interleaver_tester/dut/i0/*
add wave -group "Asynchronous Bridge"
add wave -group "Asynchronous Bridge" -ports /interleaver_tester/dut/i1/*
add wave -expand -group "Memory Controller"
add wave -group "Memory Controller" -ports /interleaver_tester/dut/mc0/*
add wave -expand -group "SRAM #1"
add wave -group "SRAM #1" /interleaver_tester/dut/m1/CLK
add wave -group "SRAM #1" /interleaver_tester/dut/m1/PD
add wave -group "SRAM #1" /interleaver_tester/dut/m1/CEB_i
add wave -group "SRAM #1" /interleaver_tester/dut/m1/WEB_i
add wave -group "SRAM #1" -unsigned /interleaver_tester/dut/m1/A_i
add wave -group "SRAM #1" -unsigned /interleaver_tester/dut/m1/D
add wave -group "SRAM #1" -unsigned /interleaver_tester/dut/m1/Q
}

pa msg -disable -pa_checks=irc
pa msg -stopafter 5 -pa_checks=rsa
pa msg -stopafter 5 -pa_checks=rtc

run -all
pa msg -disable -pa_checks=r

run -continue
if {![batch_mode]} {
wave zoomrange 156400ns 185000ns
}
coverage report -detail -pa
coverage save -pa pa.ucdb
vcover report pa.ucdb -pa

if {[batch_mode]} {
    quit -f
}
