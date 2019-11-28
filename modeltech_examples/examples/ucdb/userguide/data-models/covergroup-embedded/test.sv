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
    class c;
        int i;
        covergroup cg;
            coverpoint i { bins ival[] = { [0:1] }; }
        endgroup
        function new();
            cg = new;
        endfunction
        function void sample(int val);
            i = val;
            cg.sample();
        endfunction
    endclass
endpackage
module top;
    p::c cv = new;
    initial begin
        cv.sample(0);
        $display($get_coverage());
    end
endmodule
