//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// SystemVerilog Constrained Random Example - Component to be tested
//
module DUT(clock,px_in,px_out);

    import Global::*; // use Verilog-1995 ports, import can go here
    input logic clock;
    input RGB_t px_in[N];
    output RGB_t px_out[N];
   
    // DUT just checks that data arrives
    genvar i;
    for (i=0;i<N;i++) begin
        always @(posedge clock) begin 
 	        $display("Pixel%0d is %h,%h,%h at %t",
                i, px_in[i].R, px_in[i].G, px_in[i].B, $time);
            px_out <= px_in;
        end
    end
  
endmodule : DUT
