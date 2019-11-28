//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog DPI Example - Verilog test module for 8-to-1 MUX
//
`timescale 1ns / 1ns

module top;

    parameter CLK_PD = 100;               // system clock period

    logic [7:0] data;                     // DUT input signals
    logic [2:0] select;                   //
    logic enable_b;                       //
    wire y_l, w_l;                        // DUT output signals
    bit clock = 0;                        // testbench clock
    logic [1:0] results [0:127];          // array to hold golden test values
    int e_cnt = 0;                        // counter for DATA MISMATCHES
    int v_cnt = 0;                        // verification counter

    ///////////////////////////////////////////////
    // Device Under Test: 8-to-1 multiplexer
    ///////////////////////////////////////////////
    MUX81 DUT (
        .D0(data[0]),
        .D1(data[1]),
        .D2(data[2]),
        .D3(data[3]),
        .D4(data[4]),
        .D5(data[5]),
        .D6(data[6]),
        .D7(data[7]),
        .S0(select[0]),
        .S1(select[1]),
        .S2(select[2]),
        .ENb(enable_b),
        .W(w_l),
        .Y(y_l));

    // clock generator
    always
        #(CLK_PD/2) clock = ~clock;

    // simulation control
    initial begin
        //////////////////////////////////////////////////////////////////////
        // load results array
        //////////////////////////////////////////////////////////////////////
        $readmemb("mux81.dat", top.results);
        //////////////////////////////////////////////////////////////////////
        // stimulus
        //////////////////////////////////////////////////////////////////////
        enable_b = 1'b1;
        select = 3'b000;
        data = 8'b00000000;
        @(negedge clock) vdata;
        data = 8'b01010101;
        @(negedge clock) vdata;
        enable_b = 1'b0;
        data = 8'b00000000;
        @(negedge clock) vdata;
        data = 8'b00000001;
        @(negedge clock) vdata;
        data = 8'b00000000;
        @(negedge clock) vdata;
        select = 3'b001;
        @(negedge clock) vdata;
        data = 8'b00000010;
        @(negedge clock) vdata;
        data = 8'b00000000;
        @(negedge clock) vdata;
        select = 3'b010;
        @(negedge clock) vdata;
        data = 8'b00000100;
        @(negedge clock) vdata;
        data = 8'b00000000;
        @(negedge clock) vdata;
        select = 3'b011;
        @(negedge clock) vdata;
        data = 8'b00001000;
        @(negedge clock) vdata;
        data = 8'b00000000;
        @(negedge clock) vdata;
        select = 3'b100;
        @(negedge clock) vdata;
        data = 8'b00010000;
        @(negedge clock) vdata;
        data = 8'b00000000;
        @(negedge clock) vdata;
        select = 3'b101;
        @(negedge clock) vdata;
        data = 8'b00100000;
        @(negedge clock) vdata;
        data = 8'b00000000;
        @(negedge clock) vdata;
        select = 3'b110;
        @(negedge clock) vdata;
        data = 8'b01000000;
        @(negedge clock) vdata;
        data = 8'b00000000;
        @(negedge clock) vdata;
        select = 3'b111;
        @(negedge clock) vdata;
        data = 8'b10000000;
        @(negedge clock) vdata;
        data = 8'b00000000;
        @(negedge clock) vdata;
        data = 8'b11111011;
        @(negedge clock) vdata;
        data = 8'b00111110;
        @(negedge clock) vdata;
        //////////////////////////////////////////////////////////////////////
        // finish simulation
        //////////////////////////////////////////////////////////////////////
        $display("\n# Simulation finished: DATA MISMATCHES = %0d\n", e_cnt);
        $finish;
    end

    // verify results and maintain error count
    task vdata;
        if ({y_l, w_l} !== results[v_cnt]) begin
            ++e_cnt;
            $display("# ERROR: %b != %b", {y_l, w_l}, results[v_cnt]);
        end
        ++v_cnt;
    endtask

endmodule

module MUX81 (
    output Y, W,
    input  D0, D1, D2, D3, D4, D5, D6, D7, S0, S1, S2, ENb);

    // Make C function visible to verilog code
    import "DPI-C" context function int mux81 (
        input int select,
        input int i0, i1, i2, i3, i4, i5, i6, i7);

    // 8-to-1 multiplexer
    reg im0;
    reg [2:0] SELECT;
    always @(D0, D1, D2, D3, D4, D5, D6, D7, S0, S1, S2, ENb) begin
        SELECT = {S2, S1, S0};
        if (ENb == 1'b0)
            im0 = mux81(SELECT, D0, D1, D2, D3, D4, D5, D6, D7);
        else
            im0 = 1'b0;
    end

    // output logic
    assign Y = im0;
    assign W = ~im0;

endmodule
