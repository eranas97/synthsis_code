`timescale 1ns/1ns

`celldefine
module PAD_IN (input PAD, output C);
	buf (C, PAD);
	specify
		(PAD => C)=(0, 0);
	endspecify
endmodule
`endcelldefine

`celldefine
module PAD_OUT (input I, output PAD);
	buf (PAD, I);
	specify
		(I => PAD)=(0, 0);
	endspecify
endmodule
`endcelldefine
