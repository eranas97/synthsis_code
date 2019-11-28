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

    // Verilog module instance
    ringbuf* chip;

    SC_CTOR(test_ringbuf)
      : iclock("iclock"),
        reset("reset"),
        txda("txda"),
        rxda("rxda"),
        txc("txc"),
        outstrobe("outstrobe")
    {
        const char* generic_list[5];

        generic_list[0] = strdup("int_param=4");
        generic_list[1] = strdup("real_param=2.6");
        generic_list[2] = strdup("str_param=\"Hello\"");
        generic_list[3] = strdup("bit_param=1'b0");
        generic_list[4] = strdup("lv_param=4'b01xz");

        // Create Verilog module instance.
        chip = new ringbuf("chip", "ringbuf", 5, generic_list);

        // Cleanup the memory allocated for generic_list
        for (int i = 0; i < 5; i++)
            free((char*)generic_list[i]);

        // Connect ports
        chip->clock(iclock);
        chip->reset(reset);
        chip->txda(txda);
        chip->rxda(rxda);
        chip->txc(txc);
        chip->outstrobe(outstrobe);
    }

    ~test_ringbuf()
    {
        delete chip;
    }
};
