//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   

module clock(trigger, clk, rst_n);
   input	  trigger;
   output	  clk;
   output	  rst_n;
   
   reg		  clk;
   reg		  rst_n;
   reg [5:0] rcount;
   reg		  reset_init;
   
   initial 
    begin
       #25 clk = 1;
       #25 rst_n = 0;
       rcount = 0;
       reset_init = 0;
    end
   
   // Set Clock for 50ns cycles
   always
    begin
        #25 clk = ~clk;
    end
   
   // Reset stays low for 10 clock cycles
   always @(posedge clk) 
    begin
        if (reset_init == 0) 
         begin
             if (rcount < 10) 
              begin
                  rst_n = 0;
                  rcount = rcount + 1;
                  end
             else
              begin
                  rst_n = 1;
                  reset_init = 1;
                  rcount = 0;
                  end
             end
        end

   // Set the trigger
   always @(posedge trigger)
    begin
        reset_init = 0;
    end

endmodule
