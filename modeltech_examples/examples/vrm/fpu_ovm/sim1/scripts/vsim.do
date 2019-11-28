onerror {resume}
onbreak {resume}
onElabError {resume}

# Simulation specific setup
set StdArithNoWarnings   1
set NumericStdNoWarnings 1

if {[batch_mode]} {
	 source wave_batch.do
} else {
	 source wave.do
}

# Start the simulation
run -a        

# Save coverage, and prepare for next run...
coverage attr  -name TESTNAME -value [format "%s_%d"   [file rootname $env(UCDBFILE)] $Sv_Seed]
coverage save      [format "%s"       $env(UCDBFILE) ]

#quit -sim

quit
