//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// SystemVerilog Dynamic Array of Classes Example - Global Package
//
package DynPkg;

    class CELL;
        rand bit [3:0] A, B, C;
        constraint C1 {
            A inside{[0:7]};                     // Constrain A & B to avoid
            B inside{[0:7]};                     // overflow on C
            C == B + A ;
        }
    endclass
 
    class ROW;
        rand CELL C_Array[];                     // dynamic array of CELL
    endclass


    class FRAME;
        rand ROW R_Array[];                      // dynamic array of ROW
        function new (int DEPTH, int WIDTH) ;
            R_Array = new[DEPTH];                // initialize ROW array
            for(int i = 0; i < DEPTH; i++) begin
                R_Array[i] = new;                // construct each ROW inst
                R_Array[i].C_Array = new[WIDTH]; // initialize CELL array
                for(int j = 0; j < WIDTH; j++)
                    R_Array[i].C_Array[j] = new; // construct each CELL inst
            end
        endfunction
    endclass

endpackage
