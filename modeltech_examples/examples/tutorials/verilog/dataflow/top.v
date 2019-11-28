//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   

`timescale 1 ns / 1 ns
module top;

  reg clk;

  // Processor bus signals
  wire prw, pstrb, prdy;
  wire [7:0] paddr;
  wire [15:0] pdata;

  // System bus signals
  wire srw, sstrb, srdy;
  wire [7:0] saddr;
  wire [15:0] sdata;
    
  initial begin
    clk = 1'b0;
  end
  
  always #20 clk = ~clk;

  proc p (.clk(clk), .addr(paddr), .data(pdata), 
          .rw(prw), .strb(pstrb), .rdy(prdy));
  cache c (.clk(clk), .paddr(paddr), .pdata(pdata),
           .prw(prw), .pstrb(pstrb), .prdy(prdy),
           .saddr(saddr), .sdata(sdata),
           .srw(srw), .sstrb(sstrb), .srdy(srdy));
  memory m (.clk(clk), .addr(saddr), .data(sdata),
            .rw(srw), .strb(sstrb), .rdy(srdy));

endmodule
