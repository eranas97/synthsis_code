//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog DPI Example - Verilog test module for fibonacci seq.
//
`timescale 1ns / 1ns
`define EOF -1

module top;

    parameter CLK_PD = 100;                 // system clock period
    parameter N = 46;                       // max number of sequences
    parameter TESTFILE = "./fibonacci.dat"; // test vectors

    logic [7:0] n_l;                        // DUT input
    logic [31:0] y_l;                       // DUT output
    bit clock = 0;                          // testbench clock
    logic [31:0] results [0:46];            // array of golden test values
    int FD;                                 // input file handle
    int e_cnt = 0;                          // counter for DATA MISMATCHES
    int v_cnt = 0;                          // verification counter
    int l_cnt = 0;                          // counter - loading results array

    // Make C function visible to verilog code
    import "DPI-C" context function int unsigned fibonacci(input int unsigned N);

    // clock generator
    always
        #(CLK_PD/2) clock = ~clock;

    // simulation control
    initial begin
        // Open input file - break simulation an error occurs
        FD = $fopen(TESTFILE, "r");
        if (FD == 0) begin
            $display("# ERROR: Failure opening \"%s\" for READING", TESTFILE);
            $finish;
        end

        // load results array
        while ($fscanf(FD, "%d", results[l_cnt]) != `EOF)
            ++l_cnt;

        // apply stimulus
        repeat (500000) begin
            n_l = 1;
            repeat (N) begin
                y_l = fibonacci(n_l);
                @(negedge clock) vdata;
                ++n_l;
            end
        end

        $display("\n# Simulation finished: DATA MISMATCHES = %0d\n", e_cnt);
        $fclose(FD);
        $finish;
    end

    // verify results & maintain error count
    task vdata;
        if (y_l !== results[v_cnt]) begin
            ++e_cnt;
            $display("# ERROR: %0d != %0d", y_l, results[v_cnt]);
        end
        if (n_l == N)
            v_cnt = 0;
        else
            ++v_cnt;
    endtask

endmodule
