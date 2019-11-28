//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Interface Example - Testbench
//
`timescale 1ns / 1ns

module testbench;

    parameter CLK_PD = 100;               // system clock period
    parameter OUTFILE = "./output.log";   // output file for logging data

    bit clock, start, stop;               // testbench signals

    logic [15:0] results [0:127];         // array to hold golden test values
    int FD;                               // handle to file opened by $fopen
    int e_cnt = 0, v_cnt = 0;             // testbench counters

    MEM_IF I0 (                           // instance - Interface
        .CLK(clock),
        .FD);
    CONTROL I1 (                          // instance - Controller
        .IO(I0),
        .STRT(start),
        .CLK(clock),
        .STOP(stop));
    MEMORY I2 (                           // instance - Memory
        .IO(I0),
        .CLK(clock));
 
    // clock generator
    always
        #(CLK_PD/2) clock = ~clock;

    // control simulation
    initial begin
        ///////////////////////////////////////////////////////////////////
        // Open output file - exit if an error occurs opening the file
        ///////////////////////////////////////////////////////////////////
        FD = $fopen(OUTFILE);
        if (FD == 0) begin
            $display("# ERROR: Failure opening \"%s\" for WRITING", OUTFILE);
            $finish;
        end
        ///////////////////////////////////////////////////////////////////
        // format time for printing
        ///////////////////////////////////////////////////////////////////
        $timeformat(-9,0," ns", 8);
        $fdisplay(FD | 1, "\n   time       Results");
        $fdisplay(FD | 1, " --------  ------------------------------------");
        ///////////////////////////////////////////////////////////////////
        // load memories
        ///////////////////////////////////////////////////////////////////
        $readmemh("vectors.dat", testbench.I2.MEM);
        $readmemh("results.dat", testbench.results);
        ///////////////////////////////////////////////////////////////////
        // Stimulus
        ///////////////////////////////////////////////////////////////////
        @(negedge clock) start = 1;    // Start Controller
        @(negedge clock) start = 0;
        @(posedge stop);
        @(negedge clock) I0.MWR = 1;   // Test assertions in interface
        @(negedge clock) I0.MWR = 0;
        @(negedge clock) I0.MRD = 1;   // WriteBeforeRead should fail here
        @(negedge clock) I0.MRD = 0;
        @(negedge clock) I0.MWR = 1;   // ReadBeforeWrite should fail here
        @(negedge clock) I0.MWR = 0;
        ///////////////////////////////////////////////////////////////////
        // finish simulation
        ///////////////////////////////////////////////////////////////////
        $fdisplay(FD | 1, "\n Simulation finished: DATA MISMATCHES = %0d\n",
            e_cnt);
        $fclose(FD);
        $stop;
    end

    // verify result & maintain error count
    always @(posedge I0.MWR)
        if (~stop) begin
            if (I0.DATA !== results[v_cnt]) begin
                $fdisplay(FD | 1, "%t:   DATA MISMATCH: data %h: expected %h",
                    $realtime, I0.DATA, results[v_cnt]);
                ++e_cnt;
            end
            ++v_cnt;
        end
 
endmodule
