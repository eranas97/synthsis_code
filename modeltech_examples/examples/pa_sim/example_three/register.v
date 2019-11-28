`timescale 1ns/1ns

`celldefine
module register_1 (clk ,reset ,d ,q);
	
	input clk,reset;
	input  [3 : 0] d;
	output reg [3 : 0] q;
  
	always @ (posedge(clk),posedge(reset))
	begin
	if (reset)
		q <= 0;
	else
		q <= d;
	end
endmodule
`endcelldefine

`celldefine
module register_2 (clk ,reset ,d ,q);
	
	input clk,reset;
	input  [1 : 0] d;
	output reg [1 : 0] q;
  
	always @ (posedge(clk),posedge(reset))
	begin
	if (reset)
		q <= 0;
	else
		q <= d;
	end
endmodule
`endcelldefine
