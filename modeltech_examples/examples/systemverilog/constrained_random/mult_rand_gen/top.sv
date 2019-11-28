//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// SystemVerilog Constrained Random Example - Top level module
//
module top;

    import Global::*;
   
    bit clock;
    always #5 clock++;
   
    RGB_t px_in[N], px_out[N];
   
    test T1(clock,px_in,px_out);
    DUT U1(clock,px_in,px_out);
    // if connecting to a Verilog-2001 style module, then you could use:   
    // DUT U1(clock,px_in[0].R,px_in[0].G,px_in[0].B,px_in[1].R,...
   
endmodule : top
