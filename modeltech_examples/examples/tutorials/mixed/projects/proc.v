//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   

module proc(clk, addr, data, rw, strb, rdy);
    input  clk, rdy;
    output addr, rw, strb;
    inout  data;

    `define addr_size 8
    `define word_size 16

    reg [`addr_size-1:0] addr_r;
    reg [`word_size-1:0] data_r;
    reg                  rw_r, strb_r;

    reg verbose;

    wire [`addr_size-1:0] #(5) addr = addr_r;
    wire [`word_size-1:0] #(5) data = data_r;
    wire                  #(5) rw = rw_r, strb = strb_r;

    task read;
        input  [`addr_size-1:0] a;
        output [`word_size-1:0] d;
        begin
            if (verbose) $display("%t: Reading from addr=%h", $time, a);
            addr_r = a;
            rw_r = 1;
            strb_r = 0;
            @(posedge clk) strb_r = 1;
            @(posedge clk) while (rdy != 0) @(posedge clk) ;
            d = data;
        end
    endtask

    task write;
        input  [`addr_size-1:0] a;
        input  [`word_size-1:0] d;
        begin
            if (verbose) $display("%t: Writing data=%h to addr=%h", $time, d, a);
            addr_r = a;
            rw_r = 0;
            strb_r = 0;
            @(posedge clk) strb_r = 1;
            data_r = d;
            @(posedge clk) while (rdy != 0) @(posedge clk) ;
            data_r = 'bz;
        end
    endtask

    reg [`addr_size-1:0] a;
    reg [`word_size-1:0] d;
    initial begin
        // Set initial state of outputs..
        addr_r = 0;
        data_r = 'bz;
        rw_r = 0;
        strb_r = 1;
        verbose = 1;

        forever begin
            // Wait for first clock, then perform read/write test
            @(posedge clk)
            if (verbose) $display("%t: Starting Read/Write test", $time);

            // Write 10 locations
            for (a = 0; a < 10; a = a + 1)
                write(a, a);

            // Read back 10 locations
            for (a = 0; a < 10; a = a + 1) begin
                read(a, d);
                if (d !== a)
                    $display("%t: Read/Write mismatch; E: %h, A: %h", $time, a, d);
            end

            if (verbose) $display("Read/Write test done");
            $stop(1);
        end
    end
endmodule
