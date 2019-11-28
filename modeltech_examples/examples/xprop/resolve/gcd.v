//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Queue Example - Greatest Common Divisor Module
//

module GCD#(parameter W = 16)
(input clk,
input [W-1:0] operand_A,
input [W-1:0] operand_B,
input A_en,
input B_en,
input [1:0] A_sel,
input B_sel,
output [W-1:0] result_data,
output B_zero,
output A_lt_B);

wire [W-1:0] A;
wire [W-1:0] B;
wire [W-1:0] sub_out;
wire [W-1:0] A_out;
wire [W-1:0] B_out;

Mux3#(W) A_mux
(.d1 (operand_A),
 .d2 (B),
 .d3 (sub_out),
 .select (A_sel),
 .q (A_out));

DFF#(W) A_f
(.clk (clk),
 .en_p (A_en),
 .d_p (A_out),
 .q_np (A) );

Mux2#(W) B_mux
(.d1 (operand_B),
 .d2 (A),
 .select (B_sel),
 .q (B_out) );

DFF#(W) B_f
(.clk (clk),
 .en_p (B_en),
 .d_p (B_out),
 .q_np (B) );

assign B_zero = (B==0);
assign A_lt_B = (A < B);
assign sub_out = A - B;
assign result_data = A;

endmodule