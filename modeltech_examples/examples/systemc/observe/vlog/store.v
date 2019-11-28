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

    reg sig1_reg;
    reg sig2_reg;
    reg [3:0] sig3_reg;
    reg [0:2] sig4_reg;

    wire sig1 = sig1_reg;
    wire sig2 = sig2_reg;
    wire [3:0] sig3 = sig3_reg;
    wire [0:2] sig4 = sig4_reg;
    integer state;

    initial state = 0;

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

    always @ (posedge clock)
    begin : assign_observed_value
        if (state == 0) begin
            $display("VLOG drives sig1=1, sig2=0, sig3=1010, sig4=111");
            sig1_reg <= 'b1;
            sig2_reg <= 'b0;
            sig3_reg <= 'b1010;
            sig4_reg <= 'b111;
            state <= 1;
        end else if (state == 1) begin
            $display("VLOG drives sig1=x, sig2=x, sig3=1001, sig4=0x0");
            sig1_reg <= 'bx;
            sig2_reg <= 'bx;
            sig3_reg <= 'b1001;
            sig4_reg <= 'b0x0;
            state <= 2;
        end else begin
            $display("VLOG drives sig1=0, sig2=1, sig3=0000, sig4=100");
            sig1_reg <= 'b0;
            sig2_reg <= 'b1;
            sig3_reg <= 'b0000;
            sig4_reg <= 'b100;
            state <= 0;
        end
    end

endmodule
