//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Queue Example - Top Level Module
//

module top #(parameter W = 16) (operand_A, operand_B, clk, reset, result_data);

input [W-1:0] operand_A, operand_B;
input clk, reset;
output [W-1:0] result_data;

reg A_en, B_en, B_sel, input_available, result_rdy;
wire B_zero, A_lt_B;
reg [1:0] A_sel;

GCD G1 (clk, operand_A, operand_B, A_en, B_en, A_sel, B_sel, result_data, B_zero, A_lt_B);
  
localparam WAIT = 2'd0;
localparam CALC = 2'd1;
localparam DONE = 2'd2;

reg [1:0] state_next;
wire [1:0] state;

RDFF #(2, WAIT)
state_pf
(.clk (clk),
 .reset (reset),
 .d (state_next),
 .q (state));

always @(*)
begin
 A_sel = 2'bx;
 A_en  = 0;
 B_sel = 1'bx;
 B_en  = 0;
 input_available = 0;
 result_rdy = 0;
 case (state)
 WAIT: begin
  A_sel = 0;
  A_en  = 1;
  B_sel = 0;
  B_en  = 1;
  input_available = 1;
 end
 CALC: if (A_lt_B) begin
    A_sel = 2'b01;
    A_en  = 1;
    B_sel = 1;
    B_en  = 1;
  end
  else if (!B_zero) begin
    A_sel = 2'b10;
    A_en  = 1;
  end
 DONE: result_rdy = 1;
 endcase
end

always @(*)
begin
 state_next = state;
 case (state)
 WAIT:
  if (input_available)
   state_next = CALC;
 CALC:
  if (B_zero)
   state_next = DONE;
 DONE:
  if (result_rdy)
   state_next = WAIT;
 endcase
end
endmodule