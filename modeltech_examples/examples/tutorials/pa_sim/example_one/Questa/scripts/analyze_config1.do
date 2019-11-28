##############################################################################
# Source:    analyze_config1.do
# File:      Tcl script for processing UPF file for simulation 1
# Remarks:   Mentor Low Power tutorial
##############################################################################
onbreak {resume}
if {[batch_mode]} {
    onerror {quit -f}
}

echo "#"
echo "# NOTE: Analyzing UPF for 1st PA simulation ..."
echo "#"
vopt -work work \
     interleaver_tester +acc \
     -pa_upf ./UPF/mem_ctrl_config.upf \
     -pa_top "/interleaver_tester/dut" \
     -pa_genrpt=pa+de \
     -pa_checks=s+r+i  \
     -pa_disable=defaultoff \
     -pa_enable=highlight+debug \
     -pa_tclfile ./UPF/connect_ports.upf \
     -pa_coverage \
     -o top_opt

if {[batch_mode]} {
    quit -f
}
