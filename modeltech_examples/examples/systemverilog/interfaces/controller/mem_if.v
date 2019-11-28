//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Interface Example - Memory Interface
//
`timescale 1ns / 1ns

interface MEM_IF (input bit CLK, input int FD);

    logic [15:0] DATA;
    logic [4:0] ADDR;
    bit MRD = 0, MWR = 0;

    modport mpMEM (
        ref DATA,
        input ADDR, MRD, MWR);

    modport mpCTRL (
        import MemRead, MemWrite);

    // perform memory WRITE
    task MemWrite (input [4:0] A, input [15:0] D);
        ADDR = A;
        DATA = D;
        MWR = 0;
        @(negedge CLK) MWR = 1;
        $fdisplay(FD | 1, "%t:   WRITING memory: data %h: addr %h",
            $realtime, DATA, ADDR);
        @(negedge CLK) MWR = 0;
        @(negedge CLK);
    endtask

    // perform memory READ
    task MemRead (input [4:0] A, output [15:0] D);
        ADDR = A;
        MRD = 0;
        @(negedge CLK) MRD = 1;
        @(negedge CLK) D = DATA;
        $fdisplay(FD | 1, "%t:   READING memory: data %h: addr %h",
            $realtime, DATA, ADDR);
        MRD = 0;
        @(negedge CLK);
    endtask

    `ifdef ASSERT
        property ReadWriteBeforeFinish;
            @(posedge CLK) (MWR | MRD) |=> !(MRD | MWR) [*2];
        endproperty
        assert property (ReadWriteBeforeFinish) else
            $fdisplay(FD | 1,
                "%t:   ASSERT: R/W active before previous R/W finished.",
                    $realtime);
    `endif

endinterface
