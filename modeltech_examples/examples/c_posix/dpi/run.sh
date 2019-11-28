#!/bin/sh
#
# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
# PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
# LICENSE TERMS.
#
# Simple SystemVerilog DPI Example - Simulation shell script
#
# Usage:     Help/usage ..................... run.sh
#            Run DPI example ................ run.sh run
#            Clean directory ................ run.sh clean
#
if [ "$1" = "clean" ] ; then
	. clean.sh 
fi

if [ "$1" != "run" ] ; then
    echo ""
    echo "### Help/Usage ..................... run.sh"
    echo "### Run DPI example ................ run.sh run"
    echo "### Clean directory ................ run.sh clean"
    echo ""
	exit 0
fi

# Create the library.
rm -rf work
vlib work
if [ $? -ne 0 ]; then
    echo "ERROR: Couldn't run vlib. Make sure \$PATH is set correctly."
    exit 0
fi

# Get the simulator installation directory.
a=`which vlib 2> /dev/null`
b=`/usr/bin/dirname $a`

set_suncc=0

# Compile the HDL source(s)
vlog -sv -dpiheader cimports.h simple_calls.sv cimports.c

# Simulate the design.
vsim -c top -do "run -all; quit -f"
exit 0
