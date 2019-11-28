// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// Filename    : ringbuf.v
//
// Description : Top Level Structure of design.

`timescale 1ns / 1ns

module ringbuf (clock, reset, txda, rxda, txc, outstrobe);

    // Design Parameters Control Complete Design
    parameter counter_size = 4;  // Counter Sizes are 2,3,4,5,6...
    parameter buffer_size = 16;  // Buffer Sizes are 4,8,16,32,64...

    // Define the I/O names
    input clock, txda, reset ;
    output rxda, outstrobe, txc;

    // Define the wires that connect the design up.
    wire clock, txda, reset;
    wire outstrobe, txc, oeenable;
    wire [(counter_size*2):0] ramadrs;
    wire [(buffer_size-1):0] buffer;

    // Component intantiations
    control #(counter_size)
      block1  ( .clock(clock) ,
                .reset(reset) ,
                .ramadrs(ramadrs),
                .txc(txc),
                .oeenable(oeenable) ,
                .outstrobe(outstrobe) );

    store #(counter_size, buffer_size)
      block2  ( .clock(clock) ,
                .reset(reset) ,
                .oeenable(oeenable),
                .ramadrs(ramadrs) ,
                .buffer(buffer),
                .txda(txda) );

    retrieve #(counter_size, buffer_size)
      block3  ( .outstrobe(outstrobe),
                .ramadrs(ramadrs) ,
                .buffer(buffer),
                .rxda(rxda) );

endmodule
