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
        type_option.comment = "Example";
        option.at_least = 2;
        cvpa: coverpoint a { bins a = { 0 }; }
        cvpb: coverpoint b { bins b = { 1 }; }
        axb: cross cvpa, cvpb { type_option.weight = 2; }
    endgroup
    cg cv = new;
    initial begin
        #1; a = 0; b = 1; cv.sample();
        #1; a = 1; b = 1; cv.sample();
        #1; $display($get_coverage());
    end
endmodule
