`timescale 1ns/1ns

module alu (in1,in2,sel,out1);
  input [3:0] in1,in2;
  input [1:0] sel;
  output [3:0] out1;
  
wire [3:0] out_and,out_or,out_xor,out_xnor;

and_cell and_gate (in1,in2,out_and);
or_cell or_gate (in1,in2,out_or);
xor_cell xor_gate (in1,in2,out_xor);
xnor_cell xnor_gate (in1,in2,out_xnor);
  
mux_cell mux_gate (out_and,out_or,out_xor,out_xnor,sel,out1);

endmodule

module and_cell (
	input [3:0] in1,in2,
	output [3:0] out1);

assign out1 = in1 & in2;

endmodule

module or_cell (
	input [3:0] in1,in2,
	output [3:0] out1);

assign out1 = in1 | in2;

endmodule

module xor_cell (
	input [3:0] in1,in2,
	output [3:0] out1);

assign out1 = in1 ^ in2;

endmodule

module xnor_cell (
	input [3:0] in1,in2,
	output [3:0] out1);

assign out1 = ~(in1 ^ in2);

endmodule
