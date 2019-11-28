//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//

module send_receive;
	import common_vl_pack::*;

	reg clk;
	vl_rec data_sent;
	vl_rec data_received;

	initial begin
		clk <= 1'b0;
		forever #5 clk = ~clk;
	end

	initial begin
		#50 $stop;
	end

	always @ (clk)
	begin
		data_sent.vl_bit <= $random%2;
		data_sent.vl_arr[3] <= $random%2;
		data_sent.vl_arr[2] <= $random%2;
		data_sent.vl_arr[1] <= $random%2;
		data_sent.vl_arr[0] <= $random%2;
	end

	always @ (data_received.vl_bit, data_received.vl_arr)
		$display("time = %02d ns @ data_sent = %p, data_received = %p", $time, data_sent, data_received);

	receive_send inst_receive_send (clk, data_sent, data_received);
endmodule
