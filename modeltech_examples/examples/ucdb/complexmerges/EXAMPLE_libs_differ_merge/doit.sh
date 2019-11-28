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
# Simple Verification Management UCDB Example - Simulation shell script
#
# Usage:     Help/usage ..................... doit.sh
#            Run csv2ucdb example ........... doit.sh run [platform]
#            Clean directory ................ doit.sh clean
#
if [ "$1" = "clean" ] ; then
    rm -f transcript *.wlf core* *.log workingExclude.cov *._lock
    rm -f *.dll *.exp *.lib *.obj *.sl *.o *.so *.ucdb csv2ucdb
    rm -f vsim_stacktrace.vstf
    rm -rf work
    exit 0
fi

if [ "$1" != "run" ] ; then
    echo ""
    echo "### Help/Usage ..................... doit.sh"
    echo "### Run csv2ucdb example ........... doit.sh run [platform]"
    echo "### Clean directory ................ doit.sh clean"
    echo ""
fi

# The rest of the script is "run"
if [ -z "$MTI_HOME" ] ; then
    echo "ERROR: Environment variable MTI_HOME is not set"
    exit 0
fi
`vsim -version | grep "64 vsim" > /dev/null`
if [ $? -eq 0 ]; then
    MTI_VCO_MODE=64
else
    MTI_VCO_MODE=32
fi
export MTI_VCO_MODE
if [ "X$2" != "X" ] ; then
	platform=$2
	echo "Platform set to $platform"
else
	platform=`$MTI_HOME/vco`
fi

dir=`pwd`
name=`basename $dir`

if [ ! -f ../common_ucdbs/topFINAL_testAwork.ucdb ] ; then
    cd ../setup
    sh doit.sh run
    cd $dir
fi

echo ""
echo "### NOTE: Running '.../complexmerges/$name/doit.sh'."
echo ""

#
#	Run:
#
vsim -c -vopt -do test.do

exit 0
