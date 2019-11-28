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

module MUX41 (
    output Y,
    input D0, D1, D2, D3, S0, S1, ENb);

    reg y_l;

    always @*
        if (ENb == 1'b0)
            case ({S1, S0})
                2'b00   : y_l = D0;
                2'b01   : y_l = D1;
                2'b10   : y_l = D2;
                2'b11   : y_l = D3;
                default : y_l = 1'bx;
            endcase
        else
            y_l = 1'b0;
    
    buf (Y, y_l);

endmodule
