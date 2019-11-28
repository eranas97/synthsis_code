##############################################################################
# Source:    liberty_gls.do
# File:      Tcl script for reading liberty files and creating
#            liberty attribute library for GLS PA simulation
# Remarks:   Mentor Low Power tutorial
##############################################################################

onbreak {resume}
if {[batch_mode]} {
    onerror {quit -f}
}

vopt -libertyfiles=./Libraries/isolation/isolation.lib,./Libraries/retention/retention.lib,./Libraries/level_shift/level_shift.lib -pa_dumplibertydb=qpa_liberty_lib

if {[batch_mode]} {
    quit -f
}
