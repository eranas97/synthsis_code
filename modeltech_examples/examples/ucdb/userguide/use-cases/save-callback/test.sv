// UCDB API User Guide Example
//
// Copyright 2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.

module top;
    reg in, out;
    always @(out) $display(out);
    initial begin
        #1; in = 0;
        #1; in = 1;
    end
    wrapper inst(in,out);
endmodule

module wrapper(input in, output out);
    assign out = $mymodel(in);
endmodule
