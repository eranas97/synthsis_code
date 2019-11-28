`timescale 1ns/1ns

`celldefine
module mux_cell (
	input [3:0] arg1,arg2,arg3,arg4, 
	input [1:0] sel, 
	output reg [3:0] out_mux);

	always @ (sel,arg1,arg2,arg3,arg4)
	begin
		case (sel)
			3'b00:
			        out_mux = arg1;
			3'b01:
				out_mux = arg2;
			3'b10:
				out_mux = arg3;
			3'b11:
				out_mux = arg4;
			default : 
				out_mux = arg1;
		endcase
	end

endmodule
`endcelldefine

