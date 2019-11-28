// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// Filename    : store.v
//
// Description : Register storage for incoming data.

`timescale 1ns / 1ns

module store (clock, reset, oeenable, ramadrs, txda, buffer);

    parameter counter_size = 4;
    parameter buffer_size = 16;

    // Define blocks I/O's
    input  clock, reset, oeenable, txda;
    input [(counter_size *2):0] ramadrs;
    output [buffer_size-1:0] buffer;

    // Define wires for connecting wires.
    wire  clock, reset, oeenable, txda, outstrobe, rxda;
    wire [(counter_size * 2):0] ramadrs;

    // Define Register types for storage
    reg [buffer_size-1:0] buffer;

    //
    // This block produces a n-bit register along
    // with decode logic to load each of the bits
    // in the register.
    //
    always @ (posedge clock)
    begin : Storer
        integer i;
        if (reset == 1'b0) begin
            buffer <= 0;
        end else if (oeenable == 1'b0) begin
            i = ramadrs[(counter_size * 2):(counter_size + 1)];
            buffer[i] <= txda;
        end
    end

endmodule
