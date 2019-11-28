//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// SystemVerilog Constrained Random Example - RGB package
//
package RGB_specific;

    import Global::*;

    class RGB_random;
        rand byte unsigned R;
        rand byte unsigned B;
        rand byte unsigned G;
        constraint Reds   {R>B;R>G;}
        constraint Blues  {B>R;B>G;}
        constraint Greens {G>R;G>B;}
        function void SetReds;
            Reds.constraint_mode(true);
            Greens.constraint_mode(false);
            Blues.constraint_mode(false);
        endfunction
        function void SetGreens;
            Reds.constraint_mode(false);
            Greens.constraint_mode(true);
            Blues.constraint_mode(false);
        endfunction
        function void SetBlues;
            Reds.constraint_mode(false);
            Greens.constraint_mode(false);
            Blues.constraint_mode(true);
        endfunction
        function new;
            SetReds;
        endfunction
    endclass

    class RGB_factory;
        RGB_random RGB_r=new;
        int channel;
        function new(int i);
            channel = i;
        endfunction : new
    endclass : RGB_factory

endpackage   
