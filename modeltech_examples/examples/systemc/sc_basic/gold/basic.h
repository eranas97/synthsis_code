// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// basic.h (modified header file)

#ifndef INCLUDED_BASIC
#define INCLUDED_BASIC

#include "systemc.h"

SC_MODULE( mod_a )
{
    sc_in_clk clk;

    void main_action_method()
    {
        cout << sc_delta_count()
             << " main_action_method called" << endl;
    }

    void main_action_thread()
    {
        while( true ) {
            cout << sc_delta_count()
                 << " main_action_thread called" << endl;
            wait();
        }
    }

    void main_action_cthread()
    {
        while( true ) {
            cout << sc_delta_count()
                 << " main_action_cthread called" << endl;
            wait();
        }
    }

    SC_CTOR( mod_a )
    {
        SC_METHOD( main_action_method );
        SC_THREAD( main_action_thread );
        SC_CTHREAD( main_action_cthread, clk.pos() );
    }
};

#ifdef MTI_SYSTEMC
SC_MODULE(top)
{
    sc_clock clk;
    mod_a a;

    SC_CTOR(top)
        : clk("clk", 200, SC_NS, 0.5, 0.0, SC_NS, false),
          a("a")
    {
        a.clk( clk );
    }
};
#endif

#endif
