// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// test_ringbuf.h

#include <systemc.h>
#include "ringbuf.h"

SC_MODULE(test_ringbuf)
{
    sc_signal<sc_logic> iclock;
    sc_signal<sc_logic> reset;
    sc_signal_resolved  txda;
    sc_signal_resolved  rxda;
    sc_signal<sc_logic> txc;
    sc_signal<sc_logic> outstrobe;
    sc_signal_rv<16>    buffers;

    // VHDL module instance
    ringbuf* chip;

    SC_CTOR(test_ringbuf)
      : iclock("iclock"),
        reset("reset"),
        txda("txda"),
        rxda("rxda"),
        txc("txc"),
        outstrobe("outstrobe"),
        buffers("buffers")
    {
        const char* generic_list[9];

        generic_list[0] = strdup("int_param=4");
        generic_list[1] = strdup("real_param=2.6");
        generic_list[2] = strdup("str_param=\"Hello\"");
        generic_list[3] = strdup("bool_param=false");
        generic_list[4] = strdup("char_param=Y");
        generic_list[5] = strdup("bit_param=0");
        generic_list[6] = strdup("bv_param=010");
        generic_list[7] = strdup("logic_param=Z");
        generic_list[8] = strdup("lv_param=01XZ");

        // Create instances
        chip = new ringbuf("chip", "ringbuf", 9, generic_list);

        // Cleanup the memory allocated for the generic list.
        for (int i = 0; i < 9; i++)
            free((char*)generic_list[i]);

        // Connect ports
        chip->clock(iclock);
        chip->reset(reset);
        chip->txda(txda);
        chip->rxda(rxda);
        chip->txc(txc);
        chip->outstrobe(outstrobe);
        chip->buffers(buffers);
    }

    ~test_ringbuf()
    {
        delete chip;
    }
};
