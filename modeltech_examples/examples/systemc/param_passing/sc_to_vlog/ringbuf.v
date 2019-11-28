// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// Filename    : ringbuf.v
//
// Description : Top Level Structure of design.

`timescale 1ns / 1ns

module ringbuf (clock, reset, txda, rxda, txc, outstrobe);

    // Design Parameters Control Complete Design
    parameter int_param = 0;
    parameter real_param = 2.9;
    parameter str_param = "Error";
    parameter bit_param = 1'b1;
    parameter [3:0] lv_param = 4'b11x1;

    // Define the I/O names
    input clock, txda, reset ;
    output rxda, outstrobe, txc;

    initial begin
        $display("int_param=%0d", int_param);
        $display("real_param=%g", real_param);
        $display("str_param=%s", str_param);
        $display("bit_param=%1b", bit_param);
        $display("lv_param=%4b", lv_param);
    end

endmodule
