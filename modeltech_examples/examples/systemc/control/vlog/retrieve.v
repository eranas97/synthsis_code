// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// Filename    : retrieve.v
//
// Description : Produces the output pointer logic.

`timescale 1ns / 1ns

module retrieve ( outstrobe, ramadrs , rxda, buffer );

    parameter counter_size = 0;
    parameter buffer_size = 0;

    // Define block I/O's
    input  outstrobe ;
    input [(counter_size * 2):0] ramadrs;
    output rxda;
    input [buffer_size-1:0] buffer;

    // Define wires for connecting wires.
    wire  outstrobe, rxda;
    wire [(counter_size * 2):0] ramadrs;
    wire [buffer_size-1:0] buffer;

    // Define Register types for storage
    reg rd0a;

    //
    // Produces the decode logic which pointers
    // to each location of the shift register.
    //
    always @ (buffer or ramadrs[counter_size-1:0] )
    begin: retriever
        integer i;
        i = ramadrs[counter_size-1:0];
        rd0a <= buffer[i] ;
    end

    // Assignment of receive data
    assign rxda = rd0a && outstrobe;

endmodule
