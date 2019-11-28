//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Interface Example - Memory
//
`timescale 1ns / 1ns

module MEMORY (MEM_IF.mpMEM IO, input bit CLK);

    logic [15:0] MEM [0:31];

    // Memory WRITE
    always @(posedge CLK)
        if (IO.MWR)
            MEM[IO.ADDR] <= IO.DATA;

    // Memory READ
    always @(posedge CLK)
        if (IO.MRD)
            IO.DATA = MEM[IO.ADDR];

endmodule
