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

    parameter counter_size = 0;
    parameter buffer_size = 0;

    // Define blocks I/O's
    input  clock, reset, oeenable, txda;
    input [(counter_size *2):0] ramadrs;
    output [buffer_size-1:0] buffer;

    // Define wires for connecting wires.
    wire  clock, reset, oeenable, txda, outstrobe, rxda;
    wire [(counter_size * 2):0] ramadrs;

    // Define Register types for storage
    reg [buffer_size-1:0] buffer;

    wire sig1;
    wire sig2;
    wire [3:0] sig3;
    wire [0:2] sig4;

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

    always @ sig1
    begin : display_sig1
        $display("sig1=%b", sig1);
    end
    always @ sig2
    begin : display_sig2
        $display("sig2=%b", sig2);
    end
    always @ sig3
    begin : display_sig3
        $display("sig3=%b", sig3);
    end

    always @ sig4
    begin : display_sig4
        $display("sig4=%b", sig4);
    end

endmodule
