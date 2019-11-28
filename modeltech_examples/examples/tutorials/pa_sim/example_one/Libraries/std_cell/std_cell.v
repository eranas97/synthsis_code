`timescale 1ns/1ps

`celldefine
module BUF (input I, output Z);
    buf (Z, I);
    specify
        (I => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module INV (input I, output ZN);
    not (ZN, I);
    specify
        (I => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AND2 (input A1, A2, output Z);
    and (Z, A1, A2);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AND3 (input A1, A2, A3, output Z);
    and (Z, A1, A2, A3);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
        (A3 => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AND4 (input A1, A2, A3, A4, output Z);
    and (Z, A1, A2, A3, A4);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
        (A3 => Z) = (0, 0);
        (A4 => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module OR2 (input A1, A2, output Z);
    or  (Z, A1, A2);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module OR3 (input A1, A2, A3, output Z);
    or  (Z, A1, A2, A3);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
        (A3 => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module OR4 (input A1, A2, A3, A4, output Z);
    or  (Z, A1, A2, A3, A4);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
        (A3 => Z) = (0, 0);
        (A4 => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module NAND2 (input A1, A2, output ZN);
    nand (ZN, A1, A2);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module NAND3 (input A1, A2, A3, output ZN);
    nand (ZN, A1, A2, A3);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (A3 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module NAND4 (input A1, A2, A3, A4, output ZN);
    nand (ZN, A1, A2, A3, A4);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (A3 => ZN) = (0, 0);
        (A4 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module NOR2 (input A1, A2, output ZN);
    nor (ZN, A1, A2);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module NOR3 (input A1, A2, A3, output ZN);
    nor  (ZN, A1, A2, A3);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (A3 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module NOR4 (input A1, A2, A3, A4, output ZN);
    nor (ZN, A1, A2, A3, A4);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (A3 => ZN) = (0, 0);
        (A4 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module XOR2 (input A1, A2, output Z);
    xor (Z, A1, A2);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module XNOR2 (input A1, A2, output ZN);
    xor (im0, A1, A2);
    not (ZN, im0);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module I_NAND2 (input A1, B1, output ZN);
    not (im0, A1);
    nand (ZN, im0, B1);
    specify
        (A1 => ZN) = (0, 0);
        (B1 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module I_NAND3 (input A1, B1, B2, output ZN);
    not (im0, A1);
    nand (ZN, im0, B1, B2);
    specify
        (A1 => ZN) = (0, 0);
        (B1 => ZN) = (0, 0);
        (B2 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module I_NAND4 (input A1, B1, B2, B3, output ZN);
    not (im0, A1);
    nand (ZN, im0, B1, B2, B3);
    specify
        (A1 => ZN) = (0, 0);
        (B1 => ZN) = (0, 0);
        (B2 => ZN) = (0, 0);
        (B3 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module I_NOR2 (input A1, B1, output ZN);
    not (im0, A1);
    nor  (ZN, im0, B1);
    specify
        (A1 => ZN) = (0, 0);
        (B1 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module I_NOR3 (input A1, B1, B2, output ZN);
    not (im0, A1);
    nor (ZN, im0, B1, B2);
    specify
        (A1 => ZN) = (0, 0);
        (B1 => ZN) = (0, 0);
        (B2 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module I_NOR4 (input A1, B1, B2, B3, output ZN);
    not (im0, A1);
    nor (ZN, im0, B1, B2, B3);
    specify
        (A1 => ZN) = (0, 0);
        (B1 => ZN) = (0, 0);
        (B2 => ZN) = (0, 0);
        (B3 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module HALF_ADD (input A, B, output S, CO);
    xor (S, A, B);
    and (CO, A, B);
    specify
        (A => CO) = (0, 0);
        (B => CO) = (0, 0);
        (A => S) = (0, 0);
        (B => S) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AO21 (input A1, A2, B, output Z);
    and (im0, A1, A2);
    or (Z, im0, B);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
        (B => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AO211 (input A1, A2, B, C, output Z);
    and (im0, A1, A2);
    or (Z, im0, B, C);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
        (B => Z) = (0, 0);
        (C => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AO22 (input A1, A2, B1, B2, output Z);
    and (im0, B1, B2);
    and (im1, A1, A2);
    or  (Z, im1, im0);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
        (B1 => Z) = (0, 0);
        (B2 => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AO222 (input A1, A2, B1, B2, C1, C2, output Z);
    and (im0, C1, C2);
    and (im1, B1, B2);
    and (im2, A1, A2);
    or (Z, im0, im1, im2);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
        (B1 => Z) = (0, 0);
        (B2 => Z) = (0, 0);
        (C1 => Z) = (0, 0);
        (C2 => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AO31 (input A1, A2, A3, B, output Z);
    and (im0, A1, A2, A3);
    or (Z, im0, B);
    specify
        (A1 => Z) = (0, 0);
        (A2 => Z) = (0, 0);
        (A3 => Z) = (0, 0);
        (B => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AOI21 (input A1, A2, B, output ZN);
    and (im0, A1, A2);
    nor (ZN, im0, B);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (B => ZN) = (0, 0);
    endspecify
endmodule

`celldefine
module AOI211 (input A1, A2, B, C, output ZN);
    and (im0, A1, A2);
    nor (ZN, im0, B, C);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (C => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AOI22 (input A1, A2, B1, B2, output ZN);
    and (im0, A1, A2);
    and (im1, B1, B2);
    nor (ZN, im0, im1);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (B1 => ZN) = (0, 0);
        (B2 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AOI222 (input A1, A2, B1, B2, C1, C2, output ZN);
    and (im0, A1, A2);
    and (im1, C1, C2);
    and (im2, B1, B2);
    nor (ZN, im2, im1, im0);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (B1 => ZN) = (0, 0);
        (B2 => ZN) = (0, 0);
        (C1 => ZN) = (0, 0);
        (C2 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module AOI31 (input A1, A2, A3, B, output ZN);
    and (im0, A1, A2, A3);
    nor (ZN, im0, B);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (A3 => ZN) = (0, 0);
        (B => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module OAI21 (input A1, A2, B, output ZN);
    or (im0, A1, A2);
    nand (ZN, im0, B);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (B => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module OAI22 (input A1, A2, B1, B2, output ZN);
    or (im0, A1, A2);
    or (im1, B1, B2);
    nand (ZN, im0, im1);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (B1 => ZN) = (0, 0);
        (B2 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module OAI221 (input A1, A2, B1, B2, C, output ZN);
    or (im0, A1, A2);
    or (im1, B1, B2);
    nand (ZN, im0, im1, C);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (B1 => ZN) = (0, 0);
        (B2 => ZN) = (0, 0);
        (C => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module OAI31 (input A1, A2, A3, B, output ZN);
    or  (im0, A1, A2, A3);
    nand (ZN, im0, B);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (A3 => ZN) = (0, 0);
        (B => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module IOA21 (input A1, A2, B, output ZN);
    nand (im0, A1, A2);
    nand (ZN, im0, B);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (B => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module MOAI22 (input A1, A2, B1, B2, output ZN);
    nand (im0, B1, B2);
    or (im1, A1, A2);
    nand (ZN, im0, im1);
    specify
        (A1 => ZN) = (0, 0);
        (A2 => ZN) = (0, 0);
        (B1 => ZN) = (0, 0);
        (B2 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module MUX21 (input I0, I1, S, output Z);
    mux_udp (Z, I0, I1, S);
    specify
        (I0 => Z) = (0, 0);
        (I1 => Z) = (0, 0);
        (S => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module MUX31 (input I0, I1, I2, S0, S1, output Z);
    mux_udp (im0, I0, I1, S0);
    mux_udp (Z, im0, I2, S1);
    specify
        (I0 => Z) = (0, 0);
        (I1 => Z) = (0, 0);
        (I2 => Z) = (0, 0);
        (S0 => Z) = (0, 0);
        (S1 => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module MUX41 (input I0, I1, I2, I3, S0, S1, output ZN);
    mux_udp (im0, I2, I3, S0);
    mux_udp (im1, I0, I1, S0);
    mux_udp (im2, im1, im0, S1);
    not (ZN, im2);
    specify
        (I0 => ZN) = (0, 0);
        (I1 => ZN) = (0, 0);
        (I2 => ZN) = (0, 0);
        (I3 => ZN) = (0, 0);
        (S0 => ZN) = (0, 0);
        (S1 => ZN) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module DFF (input D, CP, output Q);
    reg notifier;
    dff_udp (Q_buf, D, CP, 1'b1, 1'b1, notifier);
    buf (Q, Q_buf);
    specify
        (posedge CP => (Q+:D)) = (0, 0);
        $setuphold (posedge CP, posedge D, 0, 0, notifier);
        $setuphold (posedge CP, negedge D, 0, 0, notifier);
    endspecify
endmodule
`endcelldefine

`celldefine
module DFF_EN (input D, E, CP, output Q);
    reg notifier;
    mux_udp (DE, Q_buf, D, E);
    dff_udp (Q_buf, DE, CP, 1'b1, 1'b1, notifier);
    buf (Q, Q_buf);
    specify
        (posedge CP => (Q+:((E && D) || (!(E) && Q_buf)))) = (0, 0);
        $setuphold (posedge CP &&& E, posedge D , 0, 0, notifier);
        $setuphold (posedge CP &&& E, negedge D , 0, 0, notifier);
    endspecify
endmodule
`endcelldefine

`celldefine
module DFF_SET (input D, CP, SDN, output Q);
    reg notifier;
    buf (SDN_i, SDN);
    dff_udp (Q_buf, D, CP, 1'b1, SDN_i, notifier);
    buf (Q, Q_buf);
    specify
        (posedge CP => (Q+:D)) = (0, 0);
        $setuphold (posedge CP &&& SDN_i, posedge D , 0, 0, notifier);
        $setuphold (posedge CP &&& SDN_i, negedge D , 0, 0, notifier);
    endspecify
endmodule
`endcelldefine

`celldefine
module DFF_RST (input D, CP, CDN, output Q);
    reg notifier;
    buf (CDN_i, CDN);
    dff_udp (Q_buf, D, CP, CDN_i, 1'b1, notifier);
    buf (Q, Q_buf);
    specify
        (posedge CP => (Q+:D)) = (0, 0);
        $setuphold (posedge CP &&& CDN_i, posedge D , 0, 0, notifier);
        $setuphold (posedge CP &&& CDN_i, negedge D , 0, 0, notifier);
    endspecify
endmodule
`endcelldefine

`celldefine
module DFF_EN_RST (input D, E, CP, CDN, output Q);
    reg notifier;
    buf (CDN_i, CDN);
    mux_udp (DE, Q_buf, D, E);
    dff_udp (Q_buf, DE, CP, CDN_i, 1'b1, notifier);
    buf (Q, Q_buf);
    and (CDN_E, CDN, E);
    specify
        (posedge CP => (Q+:((E && D) || (!(E) && Q_buf)))) = (0, 0);
        $setuphold (posedge CP &&& CDN_E, posedge D , 0, 0, notifier);
        $setuphold (posedge CP &&& CDN_E, negedge D , 0, 0, notifier);
    endspecify
endmodule
`endcelldefine

primitive mux_udp (output q, input d0, d1, s);
    table
    // d0  d1  s   : q
    // -----------------
       0   ?   0   : 0 ;
       1   ?   0   : 1 ;
       ?   0   1   : 0 ;
       ?   1   1   : 1 ;
       0   0   x   : 0 ;
       1   1   x   : 1 ;
    endtable
endprimitive

primitive dff_udp (output reg q, input d, cp, cdn, sdn, notifier);
    table
    // d  cp  cdn sdn notifier : q : q+
    // ----------------------------------------------------------------------
       ?   ?   0   ?     ?     : ? :  0 ; // CDN dominate SDN
       ?   ?   1   0     ?     : ? :  1 ; // SDN is set   
       ?   ?   1   x     ?     : 0 :  x ; // SDN affect Q
       ?   ?   1   x     ?     : 1 :  1 ; // Q=1,preset=X
       ?   ?   x   1     ?     : 0 :  0 ; // Q=0,clear=X
       0 (01)  ?   1     ?     : ? :  0 ; // Latch 0
       0   *   ?   1     ?     : 0 :  0 ; // Keep 0 (D==Q)
       1 (01)  1   ?     ?     : ? :  1 ; // Latch 1   
       1   *   1   ?     ?     : 1 :  1 ; // Keep 1 (D==Q)
       ? (1?)  1   1     ?     : ? :  - ; // ignore negative edge of clk
       ? (?0)  1   1     ?     : ? :  - ; // ignore negative edge of clk
       ?   ? (?1)  1     ?     : ? :  - ; // ignore positive edge of CDN
       ?   ?   1 (?1)    ?     : ? :  - ; // ignore posative edge of SDN
       *   ?   1   1     ?     : ? :  - ; // ignore data change on steady clk
       ?   ?   ?   ?     *     : ? :  x ; // timing check violation
    endtable
endprimitive