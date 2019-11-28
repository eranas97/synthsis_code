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
# Simple UCDB Example - Simulation shell script
#
# Usage:     Help/Usage ..................... cygwin_vs.sh
#            Run UCDB example ............... cygwin_vs.sh run
#            Clean directory ................ cygwin_vs.sh clean
#
if [ "$1" = "clean" ] ; then
	. clean.sh
fi

if [ "$1" != "run" ] ; then
    echo ""
    echo "### Help/Usage ..................... cygwin_vs.sh"
    echo "### Run UCDB example ............... cygwin_vs.sh run"
    echo "### Clean directory ................ cygwin_vs.sh clean"
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
. $INSTALL_HOME/examples/c_windows/setup/setup_compiler_and_linker_paths_vs.sh

# Compile the HDL source(s).
vlog -fsmverbose -cover bsectf -sv test.v
vcom -fsmverbose -cover bsectf test.vhd

# Simulate the design and create the ucdb file.
vsim -togglenovlogints -coverage -c top -do sim.do

# Compile the C source(s).
LD=$UCDB_LD
echo $CC ucdbdump.c
$CC ucdbdump.c
echo $LD ucdbdump $UCDBLIB_STATIC
$LD ucdbdump $UCDBLIB_STATIC

# Run the UCDB application.
echo ucdbdump test.ucdb -o test.dump
./ucdbdump.exe test.ucdb -o test.dump
exit 0
