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
quietly set INSTALL_HOME [file dirname [file nativename $::env(MODEL_TECH)]]

# Set the compiler and linker paths.
if {$tcl_platform(platform) eq "windows"} {
	source $INSTALL_HOME/examples/c_windows/setup/setup_compiler_and_linker_paths_mingwgcc.tcl
} else {
	source $INSTALL_HOME/examples/c_posix/setup/setup_compiler_and_linker_paths_gcc.tcl
}

# Compile the HDL source(s)
vlog mux21.v mux41.v mux81.v mux_tb.v

# Compile the C source(s).
echo $CC vpi_user.c mti_probe.c
if { [catch {eval $CC vpi_user.c mti_probe.c} result] } {
	echo $result
}
echo $LD vpi_user.$ext vpi_user.o mti_probe.o $MTIPLILIB
if { [catch {eval $LD vpi_user.$ext vpi_user.o mti_probe.o $MTIPLILIB} result] } {
	echo $result
}

# Simulate the design.
vsim -c -pli vpi_user.$ext mux_tb
onbreak {resume}
set PathSeparator .
run -all
quit -f
