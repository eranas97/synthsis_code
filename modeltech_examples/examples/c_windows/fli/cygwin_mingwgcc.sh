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
# Simple FLI Example - Simulation shell script
#
# Usage:     Help/Usage ..................... cygwin_mingw.sh
#            Run FLI example ................ cygwin_mingw.sh run
#            Clean directory ................ cygwin_mingw.sh clean
#
if [ "$1" = "clean" ] ; then
	. clean.sh
fi

if [ "$1" != "run" ] ; then
    echo ""
    echo "### Help/Usage ..................... cygwin_mingw.sh"
    echo "### Run FLI example ................ cygwin_mingw.sh run"
    echo "### Clean directory ................ cygwin_mingw.sh clean"
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

# Set the compiler and linker paths.
. $INSTALL_HOME/examples/c_windows/setup/setup_compiler_and_linker_paths_mingwgcc.sh

# Compile the C source(s).
echo $CC dumpdes.c
$CC dumpdes.c
echo $CC gates.c
$CC gates.c
echo $CC monitor.c
$CC monitor.c
echo $LD dumpdes.so dumpdes.o $MTIPLILIB
$LD dumpdes.so dumpdes.o $MTIPLILIB
echo $LD gates.so gates.o $MTIPLILIB
$LD gates.so gates.o $MTIPLILIB
echo $LD monitor.so monitor.o $MTIPLILIB
$LD monitor.so monitor.o $MTIPLILIB

# Compile the VHDL source(s).
vcom foreign.vhd

# Simulate the design.
vsim testbench -do vsim.do
exit 0
