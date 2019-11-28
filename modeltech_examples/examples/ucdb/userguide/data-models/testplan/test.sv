// UCDB API User Guide Example
//
// Copyright 2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.

module top;
	int i = 0, j = 0;
	covergroup cg;
		coverpoint i { bins i1 = { 1 }; }
		coverpoint j { bins j1 = { 1 }; }
	endgroup
	cg cv = new;
	initial begin
		#1 j = 1;
		cv.sample();
	end	
endmodule
