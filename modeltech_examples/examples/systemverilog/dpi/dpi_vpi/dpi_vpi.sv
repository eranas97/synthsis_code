//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog DPI Example - Using VPI and DPI together
//
package VPI;

    timeunit 1ns;
    timeprecision 1ns;

    import "DPI-C" context 
        VPI_handle_by_name =
            function chandle handle_by_name(input string name);
    import "DPI-C" context
        VPI_get_value =
            function int get_value(input chandle handle);
    import "DPI-C" context 
        VPI_put_value =
            function void put_value(input chandle handle, input int value);

endpackage : VPI
