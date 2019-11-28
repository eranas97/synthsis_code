##############################################################################
# Source:    analyze_config2.do
# File:      Tcl script for processing UPF file for simulation 2
# Remarks:   Mentor Low Power tutorial
##############################################################################
onbreak {resume}
if {[batch_mode]} {
    onerror {quit -f}
}

echo "#"
echo "# NOTE: Analyzing UPF for 2nd PA simulation ..."
echo "#"
vopt -work work \
     interleaver_tester +acc \
     -pa_upf ./UPF/rtl_top.upf \
     -pa_top "/interleaver_tester/dut" \
     -pa_genrpt=pa+de \
     -pa_checks=s+r+i  \
     -pa_disable=defaultoff \
     -pa_enable=highlight+debug \
     -pa_coverage \
     -pa_tclfile ./UPF/connect_ports.upf \
     -o top_opt

if {[batch_mode]} {
    quit -f
}
