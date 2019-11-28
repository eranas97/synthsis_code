`timescale 1ns/1ns

`celldefine
module mux_cell (
	input [3:0] arg1,arg2,arg3,arg4, 
	input [1:0] sel, 
	output [3:0] out_mux,
	(* pg_type = "primary_power" *) input pwr_sup,
	(* pg_type = "primary_ground" *) input gnd_sup);

	reg [3:0] out_inter;

	always @ (sel,arg1,arg2,arg3,arg4)
	begin
		case (sel)
			3'b00:
			        out_inter = arg1;
			3'b01:
				out_inter = arg2;
			3'b10:
				out_inter = arg3;
			3'b11:
				out_inter = arg4;
			default : 
				out_inter = arg1;
		endcase
	end

	assign out_mux	=	(~pwr_sup | gnd_sup) 	? 4'bxxxx :  out_inter;

endmodule
`endcelldefine

