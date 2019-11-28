//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   

module deck(clk, deal, shuffle, dealt, shuffled, rank, suit, seed);
   input		 clk;
   input		 deal;
   input         shuffle;
   output        dealt;
   output        shuffled;
   output [3:0]  rank;
   output [1:0]  suit;
   input [15:0] seed;
   
   // Storage for the deck.
   reg [5:0]  cards[51:0];

   reg [3:0] rank;
   reg [1:0] suit;
   reg       dealt, shuffled;

   // Temps
   reg [3:0] trank;
   reg [1:0] tsuit;
   reg [5:0] tcard;

   // Misc Vars
   integer count;
   integer rand;
   integer curCard;
   integer inSeed;

   reg [15:0] regSeed;
      
   initial
    begin
        // Initial register values
        regSeed = 0;
        rank = 4'bzzzz;
        suit = 2'bzz;
        dealt = 0;
        shuffled = 0;
        
        // Set the values for the deck.
        trank = 1;
        tsuit = 0;
        curCard = 0;

        // Initialize the Deck
        for (count = 0; count < 52; count = count+1)
         begin
             tcard[3:0] = trank;
             tcard[5:4] = tsuit;
             cards[count] = tcard;
             trank = trank + 1;
             if (trank == 14)
              begin
                  tsuit = tsuit + 1;
                  trank = 1;
              end // if (trank == 13)
         end // for (count = 0; count < 52; count++)
        // Shuffle the Deck
        shuffleDeck;
    end

   // Randomize the deck from the current configuration.
   task shuffleDeck;
       begin
           // The seed provided by the TCL code is far better and more
           // random than anything else, so let's use that.
           regSeed = seed;
           for (count = 0; count < 52; count = count +1)
            begin
                // Not very random at all...
                //rand = {$random} % 52;
                rand = {$random(regSeed)} % 52;
                tcard = cards[count];
                cards[count] = cards[rand];
                cards[rand] = tcard;
            end // for (count = 0; count < 52; count = count +1)
           curCard = 0;
       end
   endtask

   // Deal a card
   always @ ( clk ) 
    begin
        // Last Phase of deal handshake
        if ((dealt == 1) && (deal == 0))
         begin
             dealt = 0;
             rank = 4'bzzzz;
             suit = 2'bzz;
             
         end
        // Asked for a card
        if ((deal == 1) && (dealt == 0))
         begin
             if (curCard > 51)
              begin
                  $display("Note: End of Deck.  Shuffling...");
                  shuffleDeck;
                  curCard = 0;
              end // if (addr > 51)
             // Deal the card
             tcard = cards[curCard];
             rank = tcard[3:0];
             suit = tcard[5:4];
             curCard = curCard + 1;
             // Signal that we've completed dealing a card
             dealt = 1;
         end // always @ ( deal )
        if (shuffle == 1)
         shuffleDeck;
    end // always @ ( clk )
   
endmodule
