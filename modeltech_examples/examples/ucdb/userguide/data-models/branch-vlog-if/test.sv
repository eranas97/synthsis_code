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
    bit x = 0;
    bit y = 0;
    always @(x or y) begin
        if (x)
            $display("x is true");
        else if (y)
            $display("y is true");
    end
    initial begin
        #1; x = 1;
        #1; x = 0;
        #1; y = 1;
    end
endmodule
