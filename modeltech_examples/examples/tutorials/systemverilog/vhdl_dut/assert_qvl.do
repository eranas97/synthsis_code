##############################################################################
# Source:    assert.do
# Date:      August 23, 2006
# Modified:  September 28, 2006
# File:      Tcl simulation script for running Questa/ModelSim
# Remarks:   Questa 6.2 interleaver demo: assertion debug with SVA & vlog DUT
##############################################################################
onbreak {resume}
if [file exists work] {
  vdel -all
}
vlib work

vlog -work work -suppress 2167 -suppress 2181 -sv -f compile.f
vlog -work work -suppress 2167 -suppress 2181 -sv -f compile_bind_qvl.f -f filelist.qvl -f filelist.ovl
vcom -work work -93 -cover bcest -f compile_vhdl.f
vopt +acc -GBUG=1 top interleaver_binds -o dbgver

vsim +nowarnTFMPC dbgver

assertion fail -r -disable /top
run -all
pause

vsim +nowarnTFMPC dbgver -assertdebug

view cover
view assertion
add wave -group "Interleave DUT" /top/dut/*
configure wave -signalnamewidth 1
