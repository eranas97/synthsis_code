# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
# WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
# OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

# Use this run.do file to run this example.
# Either bring up ModelSim and type the following at the "ModelSim>" prompt:
#     do run.do
# or, to run from a shell, type the following at the shell prompt:
#     vsim -sc22 -do run.do -c
# (omit the "-c" to see the GUI while running from the shell)

onbreak {resume}

# create library
if [file exists work] {
    vdel -all
}
vlib work

# compile and link C source files
sccom -sc22 lt_extension_mandatory.cpp -g -I. -I../common/include -I../common/include/models
sccom -sc22 lt_initiator_extension_mandatory.cpp -g -I. -I../common/include -I../common/include/models
sccom -sc22 lt_target_extension_mandatory.cpp -g -I. -I../common/include -I../common/include/models
sccom -sc22 lt_extension_mandatory_top.cpp -g -I. -I../common/include -I../common/include/models
sccom -sc22 ../common/src/report.cpp -g -I. -I../common/include -I../common/include/models
sccom -sc22 ../common/src/extension_initiator_id.cpp -g -I. -I../common/include -I../common/include/models

sccom -sc22 -link

# open debugging windows
quietly view *

# start and run simulation
vsim -sc22 sc_main
run 6147ns
quit -f
