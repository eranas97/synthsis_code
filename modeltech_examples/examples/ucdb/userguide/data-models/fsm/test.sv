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
    bit clk = 0;
    bit i = 0;
    bit reset = 1;
    enum { stR, st0 } state;
    always @(posedge clk or posedge reset)
    begin
        if (reset)
            state = stR;
        else 
            case(state)
                stR: if (i==0) state = st0;
            endcase
    end
    always #10 clk = ~clk;
    always @(state) $display(state);
    initial begin
        $display(state);
        @(negedge clk);
        @(negedge clk) reset = 0;
        @(negedge clk);
        $stop;
    end
endmodule
