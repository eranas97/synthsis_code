// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_CONTROL
#define INCLUDED_CONTROL

#include <systemc.h>

SC_MODULE(control)
{
public:
    sc_in<sc_logic>         clock;
    sc_in<sc_logic>         reset;
    sc_out<sc_lv<9> >       ramadrs;
    sc_out<sc_logic>        oeenable;
    sc_out<sc_logic>        txc;
    sc_out<sc_logic>        outstrobe;

    // Class methods
    void incrementer();
    void enable_gen();
    void outstrobe_gen();

    // Constructor
    SC_CTOR(control)
      : clock("clock"),
        reset("reset"),
        ramadrs("ramadrs"),
        oeenable("oeenable"),
        txc("txc"),
        outstrobe("outstrobe")
    {
        SC_METHOD(incrementer);
        sensitive << clock.pos();
        dont_initialize();

        SC_METHOD(enable_gen);
        sensitive << clock.pos();
        dont_initialize();

        SC_METHOD(outstrobe_gen);
        sensitive << ramadrs;
        dont_initialize();
    }


    // Empty Destructor
    ~control()
    {
    }
};


//
// This process increments the ram address.
//
inline void control::incrementer()
{
    if (reset.read() == SC_LOGIC_0)
        ramadrs.write(0);
    else
    {
        int adrs_tmp = ramadrs.read().get_word(0);
        ramadrs.write(adrs_tmp + 1);
    }
}


//
// This process generates the output enable signal.
//
inline void control::enable_gen()
{
    if (reset.read() == 0)
        oeenable.write(SC_LOGIC_0);
    else
    {
        if (ramadrs.read().range(4, 0) == 0)
            oeenable.write(SC_LOGIC_1);
        else
            oeenable.write(SC_LOGIC_0);
    }
}


//
// This process generates the outstrobe and the txc data line.
//
inline void control::outstrobe_gen()
{
    sc_logic x = SC_LOGIC_1;
    for (int i = 4; i < 9; i++)
        x &= ramadrs.read()[i];

    outstrobe.write(x);
    txc.write(ramadrs.read()[4]);
}

#endif
