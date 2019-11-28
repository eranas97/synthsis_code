//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   
// Basic Algorithm
// > - Input to the module
// < - Output from the module
//
// - Begin Loop
// > Hit Play (signal + run)
// < Hand is dealt
// > Make discards (select card, turns it over) (signals asserted)
// > Hit Draw (run)
// < Replacement Cards are dealt
// < Hand is resolved
// - End Loop:
     
module play(clk, deckDeal, deckDealt, rankIn, suitIn, GUIdeal, GUIdraw, 
            rank0, suit0, discard0,
            rank1, suit1, discard1, 
            rank2, suit2, discard2, 
            rank3, suit3, discard3, 
            rank4, suit4, discard4,
            resolve, resolved
            );
   input clk;

   // Signals to/from the Deck
   input deckDealt;
   output deckDeal;
   input [3:0] rankIn;
   output [1:0] suitIn;

   // Signals to/from the GUI
   input GUIdeal;
   input GUIdraw;
   output [3:0] rank0;
   output [1:0] suit0;
   output       discard0;
   output [3:0] rank1;
   output [1:0] suit1;
   output       discard1;
   output [3:0] rank2;
   output [1:0] suit2;
   output       discard2;
   output [3:0] rank3;
   output [1:0] suit3;
   output       discard3;
   output [3:0] rank4;
   output [1:0] suit4;
   output       discard4;

   // Signals to resolver
   output resolve;
   input  resolved;

   // Local state vars
   integer state, count;
   reg deckDeal;
   reg [3:0] rank0;
   reg [1:0] suit0;
   reg [3:0] rank1;
   reg [1:0] suit1;
   reg [3:0] rank2;
   reg [1:0] suit2;
   reg [3:0] rank3;
   reg [1:0] suit3;
   reg [3:0] rank4;
   reg [1:0] suit4;
   reg resolve;
   
   initial
    begin
        // Initialization
        deckDeal = 0;
        state = 0;
        rank0 = 4'bzzzz;
        suit0 = 2'bzz;
        rank1 = 4'bzzzz;
        suit1 = 2'bzz;
        rank2 = 4'bzzzz;
        suit2 = 2'bzz;
        rank3 = 4'bzzzz;
        suit3 = 2'bzz;
        rank4 = 4'bzzzz;
        suit4 = 2'bzz;
        resolve = 0;
    end

   // Task: dealCard
   // 1) Ask for a card from the deck (assert deckDeal)
   // 2) wait until the deckDealt is asserted
   // 3) Sample the rank and suit
   // 4) Let deck know we're good (deassert deckDeal)
   // 5) Delay one extra cycle
   task dealCard;
       output [3:0] trank;
       output [1:0] tsuit;
       
       begin
           @ (clk) deckDeal = 1;
           while (deckDealt == 0)
            begin
                @ (clk);
            end
           deckDeal = 0;
           trank = rankIn;
           tsuit = suitIn;
           // One last delay cycle.
           @ (clk);
       end
   endtask // dealCard

   // task: resolveHand
   // Simple signal to the resolve module that the hand is complete
   // and handshake with it so we know it's done then move back to
   // the top of the state machine (state = 0)
   task resolveHand;
       begin
           resolve = 1;
           //$display("Waiting for resolved to test as '1'");
           while (resolved != 1)
            @ (clk);
           //$display("Resolved is now a one.  Drive resolve back to zero");
           resolve = 0;
           @ (clk);
           state = 0;
       end
   endtask // resolveHand
          
   always @ ( clk )
    begin
        if ((state == 0) && (GUIdeal == 1))
         begin
             // Deal a fresh set of cards
             dealCard(rank0, suit0);
             dealCard(rank1, suit1);
             dealCard(rank2, suit2);
             dealCard(rank3, suit3);
             dealCard(rank4, suit4);
             state = 1;
         end // if ((state = 0) && (deal = 1))
        if ((state == 1) && (GUIdraw == 1))
         begin
             //Redeal discards
             if (discard0 == 1)
              dealCard(rank0, suit0);
             if (discard1 == 1)
              dealCard(rank1, suit1);
             if (discard2 == 1)
              dealCard(rank2, suit2);
             if (discard3 == 1)
              dealCard(rank3, suit3);
             if (discard4 == 1)
              dealCard(rank4, suit4);
             state = 2;
         end // if ((state == 1) && (GUIdraw == 1))
        if (state == 2)
         begin
             // Resolve if the hand was a winner, a task is a bit of overkill...
             resolveHand;
         end
    end
   
endmodule // play
