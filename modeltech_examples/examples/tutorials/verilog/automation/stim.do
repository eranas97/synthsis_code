# Copyright 1991-2016 Mentor Graphics Corporation
#
# All Rights Reserved.
#
# THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
# MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

# setup an oscillator on the CLK input
force clk 1 50  -r 100
force clk 0 100 -r 100

# reset the clock and then count to 8'd100
force reset 1
run 100
if {[examine -decimal count] != {8'd0}} {
	echo "!!! Error: Reset failed. COUNT is [examine -decimal count]."
} else {
	echo "Reset OK. COUNT is [examine -decimal count]."
}

force reset 0
run 10000
if {[examine -decimal count] != {8'd100}} {
	echo "!!! Error: Counting to 8'd100 failed. COUNT is [examine -decimal count]."
} else {
	echo "Test passed. COUNT is [examine -decimal count]."
}
