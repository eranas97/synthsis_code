//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Queue Example - Test Bench
//

module tb#(parameter W = 16)();
  
reg [W-1:0] operand_A, operand_B;
wire [W-1:0] result_data;
reg clk, reset;

top T1 (operand_A, operand_B, clk, reset, result_data);

initial
begin
  $monitor("%d operand_A: %d, operand_B:%d, reset:%d, result_data:%d",$time, operand_A, operand_B, reset, result_data);
end

always
begin

clk = 0;
reset = 1;
operand_A = 4;
operand_B = 7;
#5

reset = 0;
#18

operand_A = 10;
operand_B = 2;
#18

operand_A = 0;
operand_B = 6;
#16

operand_A = 9;
operand_B = 9;
#18

operand_A = 22;
operand_B = 21;
reset = 1;
#5

reset = 0;
#13

reset = 1'bx;
#10

reset = 0;
#10

reset = 1;
#5
$finish;
end

always
begin
  #1 clk = ~clk;
end

endmodule