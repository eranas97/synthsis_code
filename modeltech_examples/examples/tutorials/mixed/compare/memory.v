//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   

module memory(clk, addr, data, rw, strb, rdy);
    input  clk, addr, rw, strb;
    output rdy;
    inout  data;

    `define addr_size 8
    `define word_size 16

    reg [`word_size-1:0] data_r;
    reg                  rdy_r;

    initial begin
        data_r = 'bz;
        rdy_r = 1;
    end

    wire [`addr_size-1:0] addr;
    wire [`word_size-1:0] #(5) data = data_r;
    wire                 #(5) rdy = rdy_r;
    
    reg [`word_size-1:0] mem[0:(1 << `addr_size) - 1];

    integer i;
    always @(posedge clk) if (strb == 0) begin
        i = addr;
        repeat (2) @(posedge clk) ;
        if (rw == 1)
            data_r = mem[i];
        rdy_r = 0;
        @(posedge clk)
        rdy_r = 1;
        if (rw == 0)
            mem[i] = data;
        else
            data_r = 'bz;
    end
endmodule   
