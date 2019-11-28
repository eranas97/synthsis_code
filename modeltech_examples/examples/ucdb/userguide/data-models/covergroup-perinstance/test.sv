// UCDB API User Guide Example
//
// Copyright 2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.

package p;
    covergroup cg (ref int v);
        option.per_instance = 1;
        coverpoint v { bins val[] = { [0:1] }; }
    endgroup
endpackage
module top;
    int a, b;
    p::cg cva = new(a);
    p::cg cvb = new(b);
    initial begin
        #1; a = 0; cva.sample();
        #1; b = 1; cvb.sample();
        #1; $display("cva=%.2f cvb=%.2f cva+cvb=%.2f",
                     cva.get_inst_coverage(), cvb.get_inst_coverage(),
                     p::cg::get_coverage());
    end
endmodule
