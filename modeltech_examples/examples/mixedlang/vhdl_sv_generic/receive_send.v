//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//

import common_vl_pack::*;

module receive_send(input vl_rec data_received);
	parameter bit bit_generic = 1'b1;
	parameter string string_generic= "receive_send";
	parameter vl_array array_type_generic = 4'b1001;

	always @ (data_received.vl_bit)
	begin
		$display("bit_generic = %b, string_generic = \"%s\", array_type_generic = %b", bit_generic, string_generic, array_type_generic);
		$display("data_received = %p", data_received);
		$stop;
	end
endmodule
