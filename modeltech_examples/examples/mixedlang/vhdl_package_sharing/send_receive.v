//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//

module send_receive;
	import common_vh_pack::*;

	reg clk;
	vh_arr data_sent;
	vh_arr data_received;

	initial begin
		clk <= 1'b0;
		forever #5 clk = ~clk;
	end

	initial begin
		#50 $stop;
	end

	always @ (clk)
	begin
		data_sent[3] <= $random%2;
		data_sent[2] <= $random%2;
		data_sent[1] <= $random%2;
		data_sent[0] <= $random%2;
	end

	always @ (data_received[0])
		$display("time = %02d ns @ data_sent = %p, data_received = %p", $time, data_sent, data_received);

	receive_send inst_receive_send (clk, data_sent, data_received);
endmodule
