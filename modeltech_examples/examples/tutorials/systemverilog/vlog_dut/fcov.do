##############################################################################
# Source:    fcov.do
# Date:      August 23, 2006
# Modified:  November 25, 2008
# File:      Tcl simulation script for running Questa/ModelSim
# Remarks:   Questa 6.5 interleaver demo: SV Functional Coverage
##############################################################################
onbreak {resume}
if [file exists work] {
  vdel -all
}
vlib work
vlog -suppress 2167 -suppress 2181 -sv -f compile.f
vopt +acc top -o dbgver
set WildcardFilter "Variable Constant Generic Parameter SpecParam Memory Assertion Endpoint CellInternal ImmediateAssert"
vsim -cvgperinstance +nowarnTFMPC dbgver
add wave -group "Interleave DUT" /top/dut/*
