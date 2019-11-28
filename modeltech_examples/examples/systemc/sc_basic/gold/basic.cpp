// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// basic.cpp (modified file)

#include "basic.h"

#ifdef MTI_SYSTEMC

SC_MODULE_EXPORT(top);

#else

int sc_main( int, char*[] )
{
    sc_clock clk;

    mod_a a( "a" );
    a.clk( clk );

    sc_initialize();

    return 0;
}

#endif
