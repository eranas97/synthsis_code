##############################################################################
# Source:    analyze_gls.do
# File:      Tcl script for processing UPF file for gls simulation
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
     -pa_loadlibertydb=qpa_liberty_lib \
     -pa_upf ./UPF/compile.upf \
     -pa_top "/interleaver_tester/dut" \
     -pa_genrpt=pa+de \
     -pa_checks=s+r+i  \
     -pa_enable=highlight+debug \
     -pa_gls \
     -pa_coverage \
     -o top_opt

if {[batch_mode]} {
    quit -f
}
