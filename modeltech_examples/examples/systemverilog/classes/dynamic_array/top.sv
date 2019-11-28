//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// SystemVerilog Dynamic Array of Classes Example - Top level
//
module top;

    import DynPkg::*;
    FRAME FR;
    int result;

    initial begin
        //////////////////////////////////////////////////////////////////
        // create an instance of dynamic 3x3 array & randomize
        //////////////////////////////////////////////////////////////////
        FR = new(3,3);
        result = FR.randomize();
        //////////////////////////////////////////////////////////////////
        // print header
        //////////////////////////////////////////////////////////////////
        $display("              A    B    C");
        $display("---------------------------");
        //////////////////////////////////////////////////////////////////
        // print out values of array
        //////////////////////////////////////////////////////////////////
        for(int i = 0; i < 3; i++) begin
            for(int j = 0; j < 3; j++)
                $display("CELL[%0d][%0d] = %b %b %b",
                    i, j,
                    FR.R_Array[i].C_Array[j].A,
                    FR.R_Array[i].C_Array[j].B,
                    FR.R_Array[i].C_Array[j].C);
            $display("");
        end
    end

endmodule
