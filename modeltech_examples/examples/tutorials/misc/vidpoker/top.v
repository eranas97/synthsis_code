//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   

module top;

   // System signals
   wire		trigger;          // Trigger the RESET signal to the design
   wire     clk;
   wire     reset;
   
   wire deal;
   wire dealt;
   wire shuffle;
   wire shuffled;
   wire GUIdeal;
   wire GUIdraw;
   
   wire [3:0] rank;
   wire [1:0] suit;

   wire [3:0] rank0;
   wire [1:0] suit0;
   wire       discard0;
   wire [3:0] rank1;
   wire [1:0] suit1;
   wire       discard1;
   wire [3:0] rank2;
   wire [1:0] suit2;
   wire       discard2;
   wire [3:0] rank3;
   wire [1:0] suit3;
   wire       discard3;
   wire [3:0] rank4;
   wire [1:0] suit4;
   wire       discard4;
   wire       resolve;
   wire       resolved;
   wire [3:0] value;
   wire [15:0] seed;

   reg GUIdeal_reg, GUIdraw_reg;
	
   clock clock1 (trigger, clk, reset);

   deck deck1 (clk, deal, shuffle, dealt, shuffled, rank, suit, seed);

   play play1 (clk, deal, dealt, rank, suit, GUIdeal, GUIdraw, 
               rank0, suit0, discard0, 
               rank1, suit1, discard1, 
               rank2, suit2, discard2, 
               rank3, suit3, discard3, 
               rank4, suit4, discard4, 
               resolve, resolved );

   resolver resolver1 (clk, resolve, resolved, value, shuffle, shuffled, 
                       rank0, suit0, 
                       rank1, suit1, 
                       rank2, suit2, 
                       rank3, suit3, 
                       rank4, suit4 );
   
   assign GUIdeal = GUIdeal_reg;
   assign GUIdraw = GUIdraw_reg;

   initial
    begin
        GUIdeal_reg = 0;
        GUIdraw_reg = 0;
    end

endmodule
