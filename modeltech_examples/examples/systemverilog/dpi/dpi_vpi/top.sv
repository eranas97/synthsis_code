//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog DPI Example - Using VPI and DPI together
//
module top;

    import VPI::*;

    string pathname = "top.";
    integer A=2;
    chandle my_handle;

    initial begin
    	my_handle = handle_by_name({pathname,"A"});
    	$display("top.A is %1d",get_value(my_handle));
    	put_value(my_handle, 3);
    	$display("top.A is %1d",get_value(my_handle));
        #10 $stop;
	end

endmodule
