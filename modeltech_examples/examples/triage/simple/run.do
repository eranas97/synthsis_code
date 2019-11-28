# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
# WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
# OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
#
# To run this example, bring up the simulator and type the following at the prompt:
#     do run.do
# or, to run from a shell, type the following at the shell prompt:
#     vsim -do run.do -c
# (omit the "-c" to see the GUI while running from the shell)
# Remove the "quit -f" command from this file to view the results in the GUI.
#

onerror {quit -f}
transcript on

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Create or clear the Triage database (TDB) file
triage dbfile -clear

# Compile the example design
vlog -coverAll top.sv

# Run a series of three tests with different errors/warnings/notes
foreach TEST {top1 top2 top3} {
	switch $TEST {
		top1 {
			vsim -c top -assertdebug -msgmode both -coverage -wlf top1.wlf
		}
		top2 {
			vsim -c top -assertdebug -msgmode both -coverage -wlf top2.wlf +warning
		}
		top3 {
			vsim -c top -assertdebug -msgmode both -coverage -wlf top3.wlf +warning +error
		}
	}

  echo "Running test $TEST..."
  run -all

  echo "Setting TESTNAME to $TEST..."
  coverage attr -name TESTNAME -value $TEST

  echo "Saving UCDB file..."
  coverage save $TEST.ucdb

  echo "Quitting simulation..."
  quit -sim

  echo "Importing UCDB into triage database..."
  triage dbfile -verbose -teststatusAll -severityAll -rulesfile top.xform $TEST.ucdb
}

echo "Generating Triage report..."
triage report

quit -f
