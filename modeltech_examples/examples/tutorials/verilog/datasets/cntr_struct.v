//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   

// D flipflop with positive edge clock and
// high asynchronous reset

module dff (d, rst, clk, q);

  input d;
  input rst;
  input clk;
  output q;
  reg q;

  // events of interest are when either the clock or reset pin
  // go high
  
  always @(posedge clk or posedge rst)
  begin

     // handle asynchronous reset -- reset when rst is high
  
    if (rst)
      q = 1'b0;
      
    // handle clock edge  
      
    else
      q = d;
  end
endmodule

// 2 to 1 mux

module mux (a, b, sel, y);

  // input declarations
  
  input a;
  input b;
  input sel;
  
  // output declarations
  
  output y;
  
  assign y = sel ? b : a;
  
endmodule


// Binary counter structural example using the dff above
// plus standard gate primitives

module cntr_struct (d, ld, rst, clk, q);

  // input declarations

  input ld;
  input rst;
  input clk;
  input [3:0] d;
  
  // output declarations
  
  output [3:0] q;
  
  // wires
  
  wire  d0int;
  wire  d1int;
  wire  d2int;
  wire  d3int;
  wire  q0n;
  wire  q2n;
  wire  p1;
  wire  p2;
  wire  p3;
  wire  p4;
  wire  p5;
  wire  p6;
  wire  p7;
  wire  sel0;
  wire  sel1;
  wire  sel2;
  wire  sel3;
  
  // structure
  // output flipflops
  
  dff  dff0(sel0, rst, clk, q[0]);
  dff  dff1(sel1, rst, clk, q[1]);
  dff  dff2(sel2, rst, clk, q[2]);
  dff  dff3(sel3, rst, clk, q[3]);
  
  // bit 0 of output ff - d input
  
  not  dforq0(d0int, q[0]);
  mux  mux0(d0int, d[0], ld, sel0);
  
  // bit 1 of output ff - d input
  
  xor  dforq1(d1int, q[0], q[1]);
  mux  mux1(d1int, d[1], ld, sel1);
  
  // bit 2 of output ff - d input
  
  not  notq0(q0n, q[0]);
  and  andp1(p1, q0n, q[2]);
  xor  xorq1q2(p2, q[1], q[2]);
  and  andp3(p3, p2, q[0]);
  or   dforq2(d2int, p1, p3);
  mux  mux2(d2int, d[2], ld, sel2);

  // bit 3 of output ff - d input
  
  not  notq2(q2n, q[2]);
  and  andp4(p4, q0n, q[3]);
  and  andp5(p5, q2n, q[3]);
  xor  xorq1q3(p6, q[1], q[3]);
  and  andp7(p7, p6, q[0], q[2]);
  or   dforq3(d3int, p4, p5, p7); 
  mux  mux3(d3int, d[3], ld, sel3);
 
endmodule
