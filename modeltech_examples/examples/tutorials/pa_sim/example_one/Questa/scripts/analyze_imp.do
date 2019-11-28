##############################################################################
# Source:    analyze_imp.do
# File:      Tcl script for processing UPF file for simulation 3
# Remarks:   Mentor Low Power tutorial
##############################################################################
onbreak {resume}
if {[batch_mode]} {
    onerror {quit -f}
}

echo "#"
echo "# NOTE: Analyzing UPF for 3rd PA simulation ..."
echo "#"
vopt -work work \
     interleaver_tester +acc \
     -pa_upf ./UPF/rtl_top_imp.upf \
     -pa_top "/interleaver_tester/dut" \
     -pa_genrpt=pa+de \
     -pa_checks=s+r+i+ul+cp+p+ugc+upc  \
     -pa_enable=highlight+debug+sndebug+autotestplan+dump1.0compatupf \
     -pa_coverage \
     -pa_tclfile ./UPF/connect_ports.upf \
     -o top_opt


if {[batch_mode]} {
    quit -f
}
