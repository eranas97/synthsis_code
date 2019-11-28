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
    int a = 0, b = 0;
    covergroup cg;
        cvpa: coverpoint a { bins azero = { 0 }; bins anonzero[] = { [1:2] }; }
        cvpb: coverpoint b { bins bzero = { 0 }; bins bnonzero[] = { [1:2] }; }
        axb: cross cvpa, cvpb;
    endgroup
    cg cv = new;
    initial begin
        #1; a = 0; b = 1; cv.sample();
        #1; a = 1; b = 1; cv.sample();
        #1; $display($get_coverage());
    end
endmodule
