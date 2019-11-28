#
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
#     vsim -c -do run.do
# (omit the "-c" to see the GUI while running from the shell)
#

# Create the library.
if [file exists work] {
    vdel -all
}
vlib work

# Get the simulator installation directory.
quietly set INSTALL_HOME [ file dirname [file normalize $::env(MODEL_TECH)]]

# Set the compiler and linker paths.
if {$tcl_platform(platform) eq "windows"} {
	source $INSTALL_HOME/examples/c_windows/setup/setup_compiler_and_linker_paths_mingwgcc.tcl
	if {$is64bit == 1 } {
		quietly set RESFILE create_filehandles64.res
		quietly set RESFILE_1 dump_filehandles64.res
	} else {
		quietly set RESFILE create_filehandles32.res
		quietly set RESFILE_1 dump_filehandles32.res
	}
} else {
	source $INSTALL_HOME/examples/c_posix/setup/setup_compiler_and_linker_paths_gcc.tcl
	quietly set RESFILE ""
	quietly set RESFILE_1 ""
}

# Compile the HDL source(s)
vlog -cover s test.sv

# Simulate the design and create the ucdb file.
vsim -coverage -c top
run -all
coverage save test.ucdb
quit -sim

# Compile the C source(s).
onerror {resume}
quietly set LD $UCDB_LD
echo $CC -std=c99 create_filehandles.c
eval $CC -std=c99 create_filehandles.c
echo $LD create_filehandles create_filehandles.o $UCDBLIB $RESFILE
eval $LD create_filehandles create_filehandles.o $UCDBLIB $RESFILE
echo $CC -std=c99 dump_filehandles.c
eval $CC -std=c99 dump_filehandles.c
echo $LD dump_filehandles dump_filehandles.o $UCDBLIB $RESFILE_1
eval $LD dump_filehandles dump_filehandles.o $UCDBLIB $RESFILE_1

# Run the UCDB application.
echo create_filehandles
create_filehandles
echo dump_filehandles test.ucdb
dump_filehandles test.ucdb

quit -f
