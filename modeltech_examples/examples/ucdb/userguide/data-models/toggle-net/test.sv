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
    bit t = 0;
    assign tnet = t;
    initial begin
        #1; t = 1;
        #1; t = 0;
    end
    bottom i(tnet);
endmodule
module bottom(input wire tnet);
    always @(tnet)
        $display(tnet);
endmodule
