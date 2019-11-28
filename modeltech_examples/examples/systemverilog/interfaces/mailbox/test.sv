//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Interface Example - Testbench for Mailbox
//

typedef struct {shortint X,Y;} Coord_t;
typedef struct {byte R,G,B;} RGB_t;

module top;

    RGB_t port1; // struct data type as port
    Mailbox_if #(Coord_t,8) port2(); // Mailbox as a port

    DUT U1(port1,port2);
    test T1(port1,port2);

endmodule : top


module test (output RGB_t port1, Mailbox_if.initiator port2);

    class RGB_random;
        rand byte R;
        rand byte B;
        rand byte G;
    endclass

    class Coord_random;
        rand int X;
        rand int Y;
    endclass

    Mailbox_if #(RGB_t) M(); // Mailbox used as an object

    RGB_random RGB_r = new;
   
    always #4.2 begin : RGB_writer
        assert (RGB_r.randomize); // always check the result of randomize
        M.put(RGB_t'{RGB_r.R,RGB_r.G,RGB_r.B}); //convert class to struct
    end
    always begin : RGB_reader
        RGB_t px;
        M.get(px);
        port1 = px;
    end

    bit [2:0] delay;
   
    Coord_random Coord_r=new;
   
    always #(delay++) begin : Coord_writer
       assert (Coord_r.randomize);
       port2.put(Coord_t'{Coord_r.X,Coord_r.Y});
    end
    initial #100 $stop;
   
endmodule : test

module DUT (input RGB_t px, Mailbox_if.slave M);

    // DUT just checks that data arrives
    always @({px.R,px.G,px.B}) // every px change (except same pixel)
        $display("Pixel is %h,%h,%h at %t",px.R,px.G,px.B,$time);

    Coord_t p;

    always begin
        M.get(p);
        $display("Coordinate is %d,%d, at %t",p.X,p.Y,$time);
        #2;
    end

endmodule : DUT
