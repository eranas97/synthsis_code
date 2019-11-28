//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// VPI routine for logging of signals from within the HDL code
//
`timescale 1ns / 1ns

`celldefine
module MUX21 (
    output Y,
    input D0, D1, S, ENb);

    not (Sb, S);
    not (EN, ENb);
    nand (im0, D0, Sb, EN);
    nand (im1, D1, S, EN);
    nand (Y, im0, im1);

    specify
        specparam t_rise = 1:1:1, t_fall = 1:1:1;
        (D0 => Y) = (t_rise, t_fall);
        (D1 => Y) = (t_rise, t_fall);
    endspecify

endmodule
`endcelldefine
