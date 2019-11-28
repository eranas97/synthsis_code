//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Queue Example - Testbench
//
`timescale 1ns / 1ns

module fifo_tb;

    parameter CLK_PD = 100;               // system clock period
    parameter TESTFILE = "./vectors.dat"; // test vectors    
    parameter OUTFILE = "./output.log";   // simulation log file

    logic [7:0] q;                        // FIFO data - output
    logic full, empty;                    // FIFO flags - output
    byte data;                            // FIFO data - input
    bit clock;                            // System clock - input
    bit nReset = 1;                       // Active-low reset - input
    bit nWrite = 1, nRead = 1;            // Active-low read/write - input
    
    byte testv [0:127];                   // array of test values
    int FD;                               // handle to file opened by $fopen
    int e_cnt = 0, v_cnt = 0, w_cnt = 0;  // testbench counters

    // device under test
    FIFO #(.DEPTH(31), .WIDTH(8)) DUT (
        .CLK(clock),
        .RSTb(nReset),
        .DATA(data),
        .Q(q),
        .WENb(nWrite),
        .RENb(nRead),
        .FULL(full),
        .EMPTY(empty));

    // clock generator
    always
        #(CLK_PD/2) clock = ~clock;

    // control simulation
    initial begin
        ///////////////////////////////////////////////////////////////////
        // Open output file - break simulation if an error occurs
        ///////////////////////////////////////////////////////////////////
        FD = $fopen(OUTFILE);
        if (FD == 0) begin
            $display("# ERROR: Failure opening \"%s\" READING", OUTFILE);
            $finish;
        end
        ///////////////////////////////////////////////////////////////////
        // format time and print header
        ///////////////////////////////////////////////////////////////////
        $timeformat(-9,0," ns", 9);
        $fdisplay(FD | 1, "\n    time         messages");
        $fdisplay(FD | 1, " ----------  ------------------------------------");
        ///////////////////////////////////////////////////////////////////
        // load test memory
        ///////////////////////////////////////////////////////////////////
        $readmemb(TESTFILE, fifo_tb.testv);
        ///////////////////////////////////////////////////////////////////
        // stimulus
        ///////////////////////////////////////////////////////////////////
        @(negedge clock);
        nReset = 0;                             // reset
        repeat (2) @(negedge clock);
        nReset = 1;
        @(negedge clock);
        nWrite = 0;                             // write 10 values
        repeat (10) begin
            data = testv[w_cnt];
            ++w_cnt;
            @(negedge clock);
        end
        nWrite = 1;
        repeat (8) @(negedge clock);            // wait a few clocks
        nRead = 0;                              // read all values out
        do
            @(negedge clock) vdata;
        while (empty != 1);
        nRead = 1;
        @(negedge clock);
        nWrite = 0;                             // write fifo until full
        while (full != 1) begin
            data = testv[w_cnt];
            ++w_cnt;
            @(negedge clock);
        end
        repeat (2) @(negedge clock);            // test writing full FIFO
        nWrite = 1;
        @(negedge clock);
        nRead = 0;                              // read out 10 values
        repeat (10) @(negedge clock) vdata;
        nRead = 1;
        @(negedge clock);
        nWrite = 0;                             // write a few more values
        repeat (6) begin
            data = testv[w_cnt];
            ++w_cnt;
            @(negedge clock);
        end
        nWrite = 1;
        @(negedge clock);
        nRead = 0;                              // read out all values
        do
            @(negedge clock) vdata;
        while (empty != 1);
        nRead = 1;
        @(negedge clock);
        nWrite = 0;                             // write more values
        repeat (15) begin
            data = testv[w_cnt];
            ++w_cnt;
            @(negedge clock);
        end
        nWrite = 1;
        @(negedge clock);
        nRead = 0;                              // read out 5 values
        repeat (5) @(negedge clock) vdata;
        nRead = 1;
        @(negedge clock);
        nReset = 0;                             // reset
        @(negedge clock);
        nReset = 1;
        @(negedge clock);
        nRead = 0;                              // test reading empty FIFO
        repeat (2) @(negedge clock);
        nRead = 1;
        repeat (2) @(negedge clock);
        ///////////////////////////////////////////////////////////////////
        // finish simulation
        ///////////////////////////////////////////////////////////////////
        $fdisplay(FD | 1, "\n Simulation finished: DATA MISMATCHES = %0d\n",
            e_cnt);
        $fclose(FD);
        $stop;
    end
    
    // verify/print result & maintain error count
    task vdata;
        if (q !== testv[v_cnt]) begin
            $fdisplay(FD | 1, "%t:    DATA MISMATCH: data %h: expected %h",
                $realtime, q, testv[v_cnt]);
            ++e_cnt;
        end
        else
            $fdisplay(FD | 1, "%t:    NOTE: Reading FIFO data = %b",
                $realtime, q);
        ++v_cnt;
    endtask

    `ifdef ASSERT
        // check illegal FIFO states
        property WriteFull;
            @(posedge clock) !nWrite |-> full != 1;
        endproperty
        property ReadEmpty;
            @(posedge clock) !nRead |-> empty != 1;
        endproperty
        assert property (WriteFull) else
            $fdisplay(FD | 1, "%t:    ASSERT: Writing full FIFO!",
                $realtime);
        assert property (ReadEmpty) else
            $fdisplay(FD | 1, "%t:    ASSERT: Reading empty FIFO!",
                $realtime);
    `endif

endmodule
