//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// SystemVerilog Constrained Random Example - Global Package
//
package Global;
   
    typedef struct {shortint X,Y;} Coord_t;
    typedef struct {byte R,G,B;} RGB_t;

    parameter N = 4;
    parameter true = 1'b1;
    parameter false = 1'b0;
   
endpackage // Global
