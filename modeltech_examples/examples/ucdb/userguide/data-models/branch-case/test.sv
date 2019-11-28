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
    int x = 0;
    always @(x)
        case (x)
            1:          $display("x is 1");
            2:          $display("x is 2");
            default:    $display("x is neither 1 nor 2");
        endcase
    initial begin
        #1; x = 1;
        #1; x = 2;
        #1; x = 3;
    end
endmodule

