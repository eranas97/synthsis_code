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
	always @ (data_received.vl_bit)
	begin
		$display("data_received = %p", data_received);
		$stop;
	end
endmodule
