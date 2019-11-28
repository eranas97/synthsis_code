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
    logic r = 1'bx;
    initial begin
        #1; r = 1'b0;
        #1; r = 1'b1;
        #1; r = 1'bz;
        #1; r = 1'b0;
        #1; r = 1'b1;
        #1; r = 1'b0;
    end
endmodule
