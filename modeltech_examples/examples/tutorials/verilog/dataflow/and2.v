//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   

`timescale 1 ns / 1 ns

///////////////////////////////////////////////////
// and2 cell:
//     Without the `celldefine compiler directive,
//     all internal primitives will be seen in the
//     dataflow window.
///////////////////////////////////////////////////
module v_and2 (input a, b,
             output y);

    buf (al, a);
    buf (bl, b);
    and (yl, al, bl);
    buf (y, yl);

    specify
        specparam t_rise = 1:1:1, t_fall = 1:1:1;
        (a => y) = (t_rise, t_fall);
        (b => y) = (t_rise, t_fall);
    endspecify

endmodule

