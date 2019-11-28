// Copyright Mentor Graphics Corporation 2005

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// basic_orig.cpp (original file)

#include "basic.h"

int sc_main( int, char*[] )
{
    sc_clock clk;

    mod_a a( "a" );
    a.clk( clk );

    sc_initialize();

    return 0;
}
