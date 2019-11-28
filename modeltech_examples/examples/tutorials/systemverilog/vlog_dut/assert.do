##############################################################################
# Source:    assert.do
# Date:      August 23, 2006
# Modified:  March 1, 2012
# File:      Tcl simulation script for running Questa/ModelSim
# Remarks:   Questa 6.5 interleaver demo: assertion debug with SVA & vlog DUT
##############################################################################
onbreak {resume}
if [file exists work] {
  vdel -all
}
vlib work

vlog -suppress 2167 -suppress 2181 -sv -f compile.f
vopt +acc -GBUG=1 top -o dbgver

vsim +nowarnTFMPC dbgver -msgmode both

assertion enable -off -r /top
run -all
pause

vsim +nowarnTFMPC  dbgver -msgmode both -assertdebug

view cover
view assertion
add wave -group "Interleave DUT" /top/dut/*
