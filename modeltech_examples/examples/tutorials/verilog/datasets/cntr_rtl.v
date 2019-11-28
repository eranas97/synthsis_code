//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   
// Binary counter example

module cntr_rtl (d, ld, rst, clk, q);

  // input declarations

  input ld;
  input rst;
  input clk;
  input [3:0] d;
  
  // output declarations
  
  output [3:0] q;
  
  // register declarations
  
  reg [3:0] q;
  
  // events of interest are when either the clock or reset pin
  // go high
  
  always @(posedge clk or posedge rst)
  begin

     // handle asynchronous reset -- reset when rst is high
  
    if (rst)
      q = 4'b0000;
      
    // handle clock edge  
      
    else
    begin
    
      // handle synchronous load
        
      if (ld)
        q = d;
      
      // handle increment
      
      else
        q = q + 1;
      
    end
  end
  
  endmodule
