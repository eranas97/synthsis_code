//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   

module resolver(clk, resolve, resolved, value, shuffle, shuffled,
            rank0, suit0,
            rank1, suit1, 
            rank2, suit2, 
            rank3, suit3, 
            rank4, suit4
            );
   input clk;
   input resolve;
   output resolved;
   output [3:0] value;
   output shuffle;
   input  shuffled;

   input [3:0] rank0;
   input [1:0] suit0;
   input [3:0] rank1;
   input [1:0] suit1;
   input [3:0] rank2;
   input [1:0] suit2;
   input [3:0] rank3;
   input [1:0] suit3;
   input [3:0] rank4;
   input [1:0] suit4;

   reg [0:3] value;
   reg resolved;
   reg shuffle;

   integer tmp, count;
   integer total, lowest, straight, threeofakind, pair, pairrank, fourofakind;
   integer sum [0:13];

   initial
    resolved = 0;
   
   always @ (clk)
    begin
        if (resolved == 1)
         begin
             // Let play know we're done and shuffle the deck
             resolved = 0;
             shuffle = 0;
         end

        // Complete handshake back to deck
        if (shuffled == 1)
         shuffle = 0;
        
        if (resolve == 1)
         begin
             shuffle = 1;
             value = 4'b0000;
             total = 0; straight = 0; pair = 0; threeofakind = 0; fourofakind = 0;
             
             // Resolve the value of the hand - sitting on rank/suit0:4
             // BTW, this is no fun at all in an HDL.  Much easier in Perl or Tcl or *something* else.

             // Some sort of flush?
             if ((suit0 == suit1) &&
                 (suit0 == suit2) &&
                 (suit0 == suit3) &&
                 (suit0 == suit4))
              begin
                  // Do some calculations to see if there is a straight going on here...
                  total = total + rank0; lowest = rank0;
                  total = total + rank1; if (rank1 < lowest) lowest = rank1;
                  total = total + rank2; if (rank2 < lowest) lowest = rank2;
                  total = total + rank3; if (rank3 < lowest) lowest = rank3;
                  total = total + rank4; if (rank4 < lowest) lowest = rank4;
                  total = total - (5*lowest);
                  // Theory goes that if it's either a royal or straight flush, the total
                  // should be 10 ((low + low+1 + low+2 + low+3 + low+4) - 5*low) = 10 if it's a straight.
                  // Or, if the answer is 42 (of course!) ((1 + 10 + 11 + 12 + 13) - 5*1) then it's a royal flush
                  if (total == 42) 
                   value = 4'b1001;    // Royal Flush
                  else
                   if (total == 10) 
                    value = 4'b1000;   // Straight Flush
                   else
                    value = 4'b0101;   // Flush
              end
             else
              begin
                  // Not a flush - Do some stuff to make deciding the hand easier
                  // Sum the total of each rank
                  for (count = 0; count < 14; count = count +1)
                   sum[count] = 0;
                  sum[rank0] = sum[rank0] + 1;
                  sum[rank1] = sum[rank1] + 1;
                  sum[rank2] = sum[rank2] + 1;
                  sum[rank3] = sum[rank3] + 1;
                  sum[rank4] = sum[rank4] + 1;
                  for (count = 1; count < 14; count = count +1)
                   begin
                       // Check for a straight
                       if (count > 4)
                        if ((sum[count] == 1)   && 
                            (sum[count-1] == 1) &&
                            (sum[count-2] == 1) &&
                            (sum[count-3] == 1) &&
                            (sum[count-4] == 1))
                         value = 4'b0100; // "Normal" Straight
                       if (count == 1)
                        if ((sum[count] == 1)   && 
                            (sum[13] == 1) &&
                            (sum[12] == 1) &&
                            (sum[11] == 1) &&
                            (sum[10] == 1))
                         value = 4'b0100; // "Wrap" Straight (10, J, Q, K, A)
                       
                       // Check for pairs, three of a kind, four of a kind, full house...
                       if (sum[count] == 2)
                        begin
                            pair = pair + 1;
                            pairrank = count;
                        end
                       if (sum[count] == 3) threeofakind = threeofakind + 1;
                       if (sum[count] == 4) fourofakind = fourofakind + 1;
                       if (fourofakind == 1)
                        value = 4'b0111; // Four of a kind
                       else 
                        if (threeofakind == 1)
                         if (pair == 1)
                          value = 4'b0110; // Full House
                         else 
                          value = 4'b0011; // Three of a kind
                        else
                         if (pair == 2)
                          value = 4'b0010; // Two pair
                         else
                          if ((pair == 1) && ((pairrank > 10)||(pairrank == 1)))
                           value = 4'b0001; // One Pair, Jacks or Better (including Aces)
                   end // for (count = 1; count < 14; count = count +1)
              end // else: !if((rank0 == rank1) &&...
             resolved = 1;
         end // if (resolve == 1)
    end // always @ (clk)
   
endmodule // resolver
