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
    bit a = 0, b = 0, clk = 0;
    always #10 clk = ~clk;
    initial begin
        @(negedge clk);        b = 1;
        @(negedge clk); a = 1; b = 0;
        @(negedge clk); a = 0; b = 1;
        @(negedge clk);        b = 0;
        @(negedge clk); $stop;
    end
    // psl default clock = rose(clk);
    // psl pslassert: assert always {b} |=> {a};
    property a_after_b;
        @(posedge clk) b |=> a;
    endproperty
    svaassert: assert property(a_after_b);
endmodule
