##############################################################################
# Source:    fcov.do
# Date:      August 23, 2006
# Modified:  September 20, 2006
# File:      Tcl simulation script for running Questa/ModelSim
# Remarks:   Questa 6.2 interleaver demo: SV Functional Coverage
##############################################################################
onbreak {resume}
if [file exists work] {
  vdel -all
}
vlib work
vlog -suppress 2167 -suppress 2181 -sv -f compile.f
vlog -work work -suppress 2167 -suppress 2181 -sv -f compile_bind_qvl.f -f filelist.qvl -f filelist.ovl
vcom -work work -93 -cover bcest -f compile_vhdl.f
vopt +acc top interleaver_binds -o dbgver
vsim +nowarnTFMPC dbgver
add wave -group "Interleave DUT" /top/dut/*
configure wave -signalnamewidth 1
