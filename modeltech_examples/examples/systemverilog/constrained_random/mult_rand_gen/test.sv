//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// SystemVerilog Constrained Random Example - testbench
//
module test(
    input bit clk,
    output Global::RGB_t pxi[Global::N],
    input Global::RGB_t pxo[Global::N]);

    import Global::*;
    import RGB_specific::*;

    // Extend the class factory to copy the class to the ports of the test
    class RGB_test extends RGB_factory;
        function new(int i);
            super.new(i);
        endfunction
        task main;
            forever @(posedge clk) begin
	            assert(RGB_r.randomize) 
	                else $fatal(0,"RGB_r randomize failed");
	            pxi[channel] = RGB_t'{RGB_r.R,RGB_r.G,RGB_r.B};
            end
        endtask : main
    endclass
   
    // Generate N threads of random class generators
    RGB_test RGB_f[N];
    genvar i;
    for (i=0;i<N;i++) begin
        initial begin 
	        RGB_f[i]=new(i);
	        RGB_f[i].main;
        end
    end

    // Start of test
    // Control all generators from one place   
    initial begin
        #40 RGB_f[1].RGB_r.SetBlues;
        $display("Pixel1 Blue");      
        #40 RGB_f[2].RGB_r.SetGreens;
        $display("Pixel2 Green");
        #40 RGB_f[3].RGB_r.SetGreens;
	    RGB_f[1].RGB_r.SetGreens;
	    RGB_f[0].RGB_r.SetGreens;
        $display("Pixels Green");
        #40 $stop;
    end
   
endmodule : test
