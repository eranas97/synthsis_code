##############################################################################
# Source:    compile_rtl.do
# File:      Tcl script for compiling RTL design with Questa
# Remarks:   Mentor Low Power Tutorial
##############################################################################
onbreak {resume}
if {[batch_mode]} {
    onerror {quit -f}
}

echo "#"
echo "# NOTE: Creating library and compiling design ..."
echo "#"
if [file exists work] {
    vdel -lib work -all
}
vlib work
vlog -work work -f ./Questa/scripts/compile_rtl.f

if {[batch_mode]} {
    quit -f
}
