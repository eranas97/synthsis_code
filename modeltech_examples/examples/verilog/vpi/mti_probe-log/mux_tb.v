//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// VPI routine for logging of signals from within the HDL code
//
`timescale 1ns / 1ns

module mux_tb;

    parameter CLK_PD = 100;               // system clock period
    parameter OUTFILE = "./output.log";   // output log file 

    reg [7:0] data;                       // test signals for DUT inputs
    reg [2:0] sel;                        //
    reg enb, clk = 1'b0;                  //
    wire y_l, w_l;                        // test signals for DUT outputs
    reg [1:0] results [0:127];            // array to hold golden test values
    integer FD;                           // handle to file opened by $fopen
    integer e_cnt = 0;                    // counter for DATA MISMATCHES
    integer v_cnt = 0;                    // counter for verification count

    // device under test
    MUX81 DUT (
        .D0(data[0]),
        .D1(data[1]),
        .D2(data[2]),
        .D3(data[3]),
        .D4(data[4]),
        .D5(data[5]),
        .D6(data[6]),
        .D7(data[7]),
        .S0(sel[0]),
        .S1(sel[1]),
        .S2(sel[2]),
        .ENb(enb),
        .W(w_l),
        .Y(y_l));

    // clock generator
    always
        #(CLK_PD/2) clk = ~clk;

    // simulation control
    initial begin
        ///////////////////////////////////////////////////////////////////
        // Test calls for $mti_probe routine
        ///////////////////////////////////////////////////////////////////
        $mti_probe("AC");
        $mti_probe("A");
        $mti_probe(DUT.I1.y_l, "C", y_l, mux_tb.DUT);
        ///////////////////////////////////////////////////////////////////
        // Open output file - break simulation if an error occurs
        ///////////////////////////////////////////////////////////////////
        FD = $fopen(OUTFILE);
        if (FD == 0) begin
            $display("# ERROR: Failure opening \"%s\" WRITING", OUTFILE);
            $finish;
        end
        ///////////////////////////////////////////////////////////////////
        // load results array
        ///////////////////////////////////////////////////////////////////
        $readmemb("results.dat", mux_tb.results);
        ///////////////////////////////////////////////////////////////////
        // stimulus
        ///////////////////////////////////////////////////////////////////
        enb  = 1'b1;
        sel  = 3'b000;
        data = 8'b00000000;
        @(negedge clk) vdata;
        data = 8'b01010101;
        @(negedge clk) vdata;
        enb  = 1'b0;
        data = 8'b00000000;
        @(negedge clk) vdata;
        data = 8'b00000001;
        @(negedge clk) vdata;
        data = 8'b00000000;
        @(negedge clk) vdata;
        sel  = 3'b001;
        @(negedge clk) vdata;
        data = 8'b00000010;
        @(negedge clk) vdata;
        data = 8'b00000000;
        @(negedge clk) vdata;
        sel  = 3'b010;
        @(negedge clk) vdata;
        data = 8'b00000100;
        @(negedge clk) vdata;
        data = 8'b00000000;
        @(negedge clk) vdata;
        sel  = 3'b011;
        @(negedge clk) vdata;
        data = 8'b00001000;
        @(negedge clk) vdata;
        data = 8'b00000000;
        @(negedge clk) vdata;
        sel  = 3'b100;
        @(negedge clk) vdata;
        data = 8'b00010000;
        @(negedge clk) vdata;
        data = 8'b00000000;
        @(negedge clk) vdata;
        sel  = 3'b101;
        @(negedge clk) vdata;
        data = 8'b00100000;
        @(negedge clk) vdata;
        data = 8'b00000000;
        @(negedge clk) vdata;
        sel  = 3'b110;
        @(negedge clk) vdata;
        data = 8'b01000000;
        @(negedge clk) vdata;
        data = 8'b00000000;
        @(negedge clk) vdata;
        sel  = 3'b111;
        @(negedge clk) vdata;
        data = 8'b10000000;
        @(negedge clk) vdata;
        data = 8'b00000000;
        @(negedge clk) vdata;
        data = 8'b11111011;
        @(negedge clk) vdata;
        data = 8'b00111110;
        @(negedge clk) vdata;
        ///////////////////////////////////////////////////////////////////
        // finish simulation
        ///////////////////////////////////////////////////////////////////
        $fdisplay(FD | 1, "\n# Simulation finished: DATA MISMATCHES = %0d\n",
            e_cnt);
        $fclose(FD);
        $stop;
    end

    // verify results & maintain error count
    task vdata;
        begin
            if ({y_l, w_l} !== results[v_cnt])
                e_cnt = e_cnt + 1;
            v_cnt = v_cnt + 1;
        end
    endtask

endmodule
