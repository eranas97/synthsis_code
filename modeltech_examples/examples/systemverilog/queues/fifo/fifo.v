//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Queue Example - Parameterized 2-state FIFO
//
//////////////////////////////////////////////////////////////////////////////
`timescale 1ns / 1ns

module FIFO #(parameter int DEPTH = 31, parameter int WIDTH = 8) (
    input bit [WIDTH-1:0] DATA,
    input bit CLK, RSTb, WENb, RENb,
    output bit FULL, EMPTY,
    output bit [WIDTH-1:0] Q);

    bit [WIDTH-1:0] mem [$:DEPTH];
  
    // FIFO write
    always @(posedge CLK, negedge RSTb)
        if (RSTb == 0)
            mem = '{};
        else if (WENb == 0 && mem.size() < DEPTH) 
            mem.push_back(DATA);

    // FIFO read
    always @(posedge CLK)
        if (RENb == 0 && mem.size() > 0)
            Q <= mem.pop_front();

    // FIFO control flags
    assign EMPTY = (mem.size() == 0) ? 1 : 0;
    assign FULL = (mem.size() == DEPTH) ? 1 : 0;

endmodule
