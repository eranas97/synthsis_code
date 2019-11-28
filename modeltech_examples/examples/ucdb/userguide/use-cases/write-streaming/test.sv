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
	enum { a, b } t;
	covergroup cg;
		coverpoint t;
	endgroup
	cg cv = new;
	initial begin
		t = b;
		cv.sample();
	end	
endmodule

