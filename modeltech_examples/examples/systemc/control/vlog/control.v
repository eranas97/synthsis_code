// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// Filename    : control.v
//
// Description : This block produces the address generation
//               and strobe generation for input and output
//               data.

`timescale 1ns / 1ns

module control (clock, reset, ramadrs, oeenable, outstrobe, txc);
    // Defines parameter value at this level
    parameter counter_size = 0;

    // Define blocks I/O's
    input  clock;
    input  reset;
    output [(counter_size * 2):0] ramadrs;
    output oeenable, txc;
    output outstrobe;

    // Define wires for connecting wires.
    wire  clock;
    wire  reset, txc;

    // Define Register types for storage
    reg [(counter_size * 2):0] ramadrs;
    reg oeenable;
    reg outstrobe;
    reg x;

    // This block creates an N-bit counter
    always @ (posedge clock)
    begin : Incrementer
        if (reset == 1'b0) begin
            ramadrs <= 0;
        end else begin
            ramadrs <= ramadrs + 1'b1;
        end
    end

    // This block generates the oeenable strobe used by the data store
    always @ (posedge clock)
    begin : Enable_gen
        if (reset == 1'b0) begin
            oeenable <= 1'b0;
        end else if (ramadrs[counter_size:0] == 0) begin
            oeenable <= 1'b1;
        end else begin
            oeenable <= 1'b0;
        end
    end

    //
    // This block implements the outstrobe
    // signal that is used to show when data output by the
    // device is valid
    //
    always @(ramadrs)
    begin: OutStrobe_gen
        integer i;
        x = 1'b1;
        for (i = counter_size; i < (counter_size * 2) + 1; i = i + 1) begin
            x = x && ramadrs[i];
        end
        outstrobe <= x;
    end

    // Assignment of the transmit clock
    assign txc = ramadrs[counter_size];

endmodule
