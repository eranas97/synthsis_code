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
# Simple UCIS Examples - Simulation shell script
#
# Usage:     Help/usage ..................... doit.sh
#            Run all examples ............... doit.sh run
#            Clean directory ................ doit.sh clean
#
if [ "$1" = "clean" ] ; then
    rm -f transcript *.wlf core* *.log workingExclude.cov
    rm -f *.dll *.exp *.lib *.obj *.sl *.o *.so *.ucis
    rm -f vsim_stacktrace.vstf
    rm -f create_ucis create_filehandles find_object test_bin_assoc
    rm -f increment_cover traverse_scopes_rs read_attrtags read_coverage formal
    rm -f read_coverage2 traverse_scopes remove_data create_ucis_ws dump_UIDs
    rm -rf work
    exit 0
fi

if [ "$1" != "run" ] ; then
    echo ""
    echo "### Help/Usage ..................... doit.sh"
    echo "### Run ucis examples .............. doit.sh run"
    echo "### Clean directory ................ doit.sh clean"
    echo ""
    echo "Some files have minor modifications to reduce compile warnings"
    echo "Some tests rely on results from earlier tests"
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
rm -f *.o *.dll *.so

case `uname` in
Linux)
    gccversion=`gcc -dumpversion | awk -F. '{print $1}'`
    machine=`uname -m`
    if [ "$MTI_VCO_MODE" = "64" ] ; then
        CC="gcc -g -c -m64 -Wall -I. -I$MTI_HOME/include"
        LD="gcc -m64 -Wl,-export-dynamic -o "
        CPP="g++ -g -c -m64 -Wall -I. -I$MTI_HOME/include"
        LPP="g++ -m64 -Wl,-export-dynamic -o "
    else
        CC="gcc -g -c -m32 -Wall -I. -I$MTI_HOME/include"
        LD="gcc -m32 -Wl,-export-dynamic -o "
        CPP="g++ -g -c -m32 -Wall -I. -I$MTI_HOME/include"
        LPP="g++ -m32 -Wl,-export-dynamic -o "
    fi
    LDLIB="$MTI_HOME/$platform/libucis.so"
    ;;
Win*|CYGWIN_NT*)
    CC="cl -c -Ox -Oy /MD -I $MTI_HOME/include "
    LD="link -INCREMENTAL:NO -DEBUG -subsystem:console"
    LDLIB="-DEFAULTLIB:$MTI_HOME/win32/ucis.lib"
    CPP="cl -c -Ox -Oy /EHsc /MD -I $MTI_HOME/include "
    LPP="link -INCREMENTAL:NO -DEBUG -subsystem:console"
    ;;
*)
    echo "Script not configured for `uname`, see User's manual."
    exit 0
    ;;
esac

echo ""
echo "### NOTE: Compiling ..."
echo ""

$CC ./src/create_filehandles.c
$CC ./src/dump_UIDs.c
$CC ./src/read_attrtags.c
$CC ./src/test_bin_assoc.c
$CC ./src/create_ucis.c
$CC ./src/find_object.c
$CC ./src/read_coverage2.c
$CC ./src/traverse_scopes.c
$CC ./src/create_ucis_ws.c
$CC ./src/read_coverage.c
$CC ./src/traverse_scopes_rs.c
$CC ./src/increment_cover.c
$CC ./src/remove_data.c
$CPP ./src/formal.cpp


echo ""
echo "### NOTE: Linking ..."
echo ""

case `uname` in
Linux)
$LD create_filehandles create_filehandles.o $LDLIB
$LD dump_UIDs dump_UIDs.o $LDLIB
$LD read_attrtags read_attrtags.o $LDLIB
$LD test_bin_assoc test_bin_assoc.o $LDLIB
$LD create_ucis create_ucis.o $LDLIB
$LD find_object find_object.o $LDLIB
$LD read_coverage2 read_coverage2.o $LDLIB
$LD traverse_scopes traverse_scopes.o $LDLIB
$LD create_ucis_ws create_ucis_ws.o $LDLIB
$LD read_coverage read_coverage.o $LDLIB
$LD traverse_scopes_rs traverse_scopes_rs.o $LDLIB
$LD increment_cover increment_cover.o $LDLIB
$LD remove_data remove_data.o $LDLIB
$LPP formal formal.o $LDLIB
    ;;
Win*|CYGWIN_NT*)
$LD -OUT:create_filehandles create_filehandles.obj $LDLIB
$LD -OUT:dump_UIDs dump_UIDs.obj $LDLIB
$LD -OUT:read_attrtags read_attrtags.obj $LDLIB
$LD -OUT:test_bin_assoc test_bin_assoc.obj $LDLIB
$LD -OUT:create_ucis create_ucis.obj $LDLIB
$LD -OUT:find_object find_object.obj $LDLIB
$LD -OUT:read_coverage2 read_coverage2.obj $LDLIB
$LD -OUT:traverse_scopes traverse_scopes.obj $LDLIB
$LD -OUT:create_ucis_ws create_ucis_ws.obj $LDLIB
$LD -OUT:read_coverage read_coverage.obj $LDLIB
$LD -OUT:traverse_scopes_rs traverse_scopes_rs.obj $LDLIB
$LD -OUT:increment_cover increment_cover.obj $LDLIB
$LD -OUT:remove_data remove_data.obj $LDLIB
$LPP -OUT:formal formal.obj $LDLIB
    ;;
esac

echo ""
echo "### NOTE: Running create_ucis (A15.1) ..."
echo ""
./create_ucis
echo ""
echo "### NOTE: Running create_filehandles (A15.2) ..."
echo ""
./create_filehandles
echo ""
echo "### NOTE: Running dump_UIDs test_API.ucis (A15.3)..."
echo ""
./dump_UIDs test_API.ucis
echo ""
echo "### NOTE: Running find_object test_API.ucis /top/cg (A15.4) ..."
echo ""
./find_object test_API.ucis /top/cg
echo ""
echo "### NOTE: Running increment_cover test_API.ucis /4:top/:5:#stmt#6#1# (A15.5) ..."
echo ""
./increment_cover test_API.ucis /4:top/:5:#stmt#6#1#
echo ""
echo "### NOTE: Running read_attrtags test_API.ucis /4:top/:5:#stmt#6#1# (A15.6) ..."
echo ""
./read_attrtags test_API.ucis /4:top/:5:#stmt#6#1#
echo ""
echo "### NOTE: Running read_coverage test_API.ucis (A15.7) ..."
echo ""
./read_coverage test_API.ucis
echo ""
echo "### NOTE: Running read_coverage2 test_API.ucis (A15.8) ..."
echo ""
./read_coverage2 test_API.ucis
echo ""
echo "### NOTE: Running traverse_scopes_rs test_API.ucis (A15.9) ..."
echo ""
./traverse_scopes_rs test_API.ucis
echo ""
echo "### NOTE: Running remove_data test_API.ucis /4:top/:5:#stmt#6#1# (A15.10) ..."
echo ""
./remove_data test_API.ucis /4:top/:5:#stmt#6#1#
echo ""
echo "### NOTE: Running traverse_scopes test_API.ucis (A15.11) ..."
echo ""
./traverse_scopes test_API.ucis
echo ""
echo "### NOTE: Running test_bin_assoc (A15.12)..."
echo ""
./test_bin_assoc
echo ""
echo "### NOTE: Running create_ucis_ws (A15.13) ..."
echo ""
./create_ucis_ws
echo ""
echo "### NOTE: Running dump_UIDs test_ws.ucis -p . (A15.3) ..."
echo ""
./dump_UIDs test_ws.ucis -p .
echo ""
echo "### NOTE: Running formal test_API.ucis (A15.14) ..."
echo ""
./formal test_API.ucis

exit 0
