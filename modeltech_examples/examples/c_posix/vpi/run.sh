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
# Simple VPI Example - Simulation shell script
#
# Usage:     Help/usage ..................... run.sh
#            Run VPI example ................ run.sh run
#            Clean directory ................ run.sh clean
#
if [ "$1" = "clean" ] ; then
	. clean.sh 
fi

if [ "$1" != "run" ] ; then
    echo ""
    echo "### Help/Usage ..................... run.sh"
    echo "### Run VPI example ................ run.sh run"
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
INSTALL_HOME=`/usr/bin/dirname $b`
set_suncc=1

# Set the compiler and linker paths. 
. $INSTALL_HOME/examples/c_posix/setup/setup_compiler_and_linker_paths_gcc.sh

# Compile the C source(s).
echo $CC vpi_test.c
$CC vpi_test.c
echo $LD vpi_test.so vpi_test.o
$LD vpi_test.so vpi_test.o

# Compile the Verilog source(s).
vlog prim.v dff.v top.v

# Simulate the design.
vsim -c -do vsim.do top -pli vpi_test.so
exit 0
