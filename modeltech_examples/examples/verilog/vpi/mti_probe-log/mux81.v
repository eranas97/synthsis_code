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

module MUX81 (
    output Y, W,
    input D0, D1, D2, D3, D4, D5, D6, D7, S0, S1, S2, ENb);

    ///////////////////////////////////////////
    // Test calls for $mti_probe routine
    ///////////////////////////////////////////
    initial
    begin
        $mti_probe(I0, "A");
        $mti_probe(I2.Sb);
        $mti_probe("C");
    end

    ///////////////////////////////////////////
    // 4-to-1 multiplexer for lower 4 bits
    ///////////////////////////////////////////
    MUX41 I0 (
        .Y(im0),
        .D0(D0),
        .D1(D1),
        .D2(D2),
        .D3(D3),
        .S0(S0),
        .S1(S1),
        .ENb(ENb));

    ///////////////////////////////////////////
    // 4-to-1 multiplexer for upper 4 bits
    ///////////////////////////////////////////
    MUX41 I1 (
        .Y(im1),
        .D0(D4),
        .D1(D5),
        .D2(D6),
        .D3(D7),
        .S0(S0),
        .S1(S1),
        .ENb(ENb));

    ///////////////////////////////////////////
    // 2-to-1 multiplexer
    ///////////////////////////////////////////
    MUX21 I2 (
        .Y(im2),
        .D0(im0),
        .D1(im1),
        .S(S2),
        .ENb(ENb));

    ///////////////////////////////////////////
    // output logic
    ///////////////////////////////////////////
    assign Y = im2;
    assign W = ~im2;

endmodule
