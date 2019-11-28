`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   21:45:30 11/26/2019
// Design Name:   vedic3bit
// Module Name:   D:/synthesis codes/multiplier/tb_vedic3bit.v
// Project Name:  multiplier
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: vedic3bit
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module tb_vedic3bit;

	// Inputs
	reg [2:0] A;
	reg [2:0] B;

	// Outputs
	wire [5:0] mul;

	// Instantiate the Unit Under Test (UUT)
	vedic3bit uut (
		.A(A), 
		.B(B), 
		.mul(mul)
	);

initial //various test inputs
begin

    $dumpfile ("vedicb.vcd");
	 $dumpvars (0, tb_vedic3bit.uut);

    A=3'b001;
    B=3'b010;

    #1 A=3'b010;
       B=3'b100;

    #1 A=3'b100;
       B=3'b101;

    #1 A=3'b101;
       B=3'b110;

    #1 A=3'b110;
       B=3'b111;
	 #10 $stop;
end
      
endmodule

