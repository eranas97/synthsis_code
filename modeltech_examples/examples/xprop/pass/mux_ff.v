//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Queue Example - Muliplexers and Flip-Flops
//

module DFF #(parameter W = 16)
(
  input              clk,
  input      [W-1:0] d_p,
  input              en_p,
  output reg [W-1:0] q_np
);   

  always @(posedge clk)
    if (en_p) q_np <= d_p;
endmodule

module RDFF #(parameter W = 1, parameter RESET_VALUE = 0)
(
  input              clk,
  input              reset,
  input      [W-1:0] d,
  output reg [W-1:0] q
);   

  always @(posedge clk)
    if (reset)
      q <= RESET_VALUE;
    else
      q <= d;
endmodule

module Mux3 #(parameter W = 16)(d1, d2, d3, select, q);

input [W-1:0] d1;
input [W-1:0] d2;
input [W-1:0] d3;
input [1:0] select;
output [W-1:0] q;

reg [W-1:0] q;
wire [1:0] select;
wire [W-1:0] d1, d2, d3;

always @(select or d1 or d2 or d3)
begin
   if (select == 0)
      q = d1;
   if (select == 2'b01)
      q = d2;
   if (select == 2'b10)
      q = d3;
end
endmodule

module Mux2 #(parameter W = 16)(d1, d2, select, q);

input [W-1:0] d1, d2;
input select;
output [W-1:0] q;

reg [W-1:0] q;
wire select;
wire [W-1:0] d1, d2;

always @(select or d1 or d2)
begin
   case (select)
       0 : q = d1;
       1 : q = d2;
   endcase
end
endmodule