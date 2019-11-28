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
    logic a = 0;
    logic b = 0;
    assign c = (a|b);
    always @(c)
        if (a || b)
            $display("a or b");
    initial begin
        #1; a = 1;
        #1; a = 0;
        #1; a = 1'bx;
    end
endmodule
