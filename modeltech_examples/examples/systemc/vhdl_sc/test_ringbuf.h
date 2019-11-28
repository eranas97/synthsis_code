// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_TEST_RINGBUF
#define INCLUDED_TEST_RINGBUF

#include <systemc.h>

#include "ringbuf.h"

SC_MODULE(test_ringbuf)
{
    // Clock period set to 5MHz
    sc_clock clock;

    sc_event reset_deactivation_event;

    sc_signal<sc_logic> iclock;
    sc_signal<sc_logic> reset;
    sc_signal<sc_logic> txda;
    sc_signal<sc_logic> rxda;
    sc_signal<sc_logic> txc;
    sc_signal<sc_logic> outstrobe;

    sc_signal<sc_lv<20> > pseudo;
    sc_signal<sc_lv<20> > storage;
    sc_signal<sc_logic> expected;
    sc_signal<sc_logic> dataerror;
    sc_signal<sc_logic> actual;

    // module instances
    ringbuf* ring_INST;

    void reset_generator();
    void generate_data();
    void compare_data();
    void print_error(); // negedge data
    void print_restore();
    void clock_assign();

    // Constructor
    SC_CTOR(test_ringbuf)
      : clock("clock", 200, 0.5, 0.0, false),
        iclock("iclock"),
        reset("reset"),
        txda("txda"),
        rxda("rxda"),
        txc("txc"),
        outstrobe("outstrobe"),
        pseudo("pseudo"),
        storage("storage"),
        expected("expected"),
        dataerror("dataerror"),
        actual("actual")
    {
        // Create instances
        ring_INST = new ringbuf("ring_INST");

        // Connect ports
        ring_INST->clock(iclock);
        ring_INST->reset(reset);
        ring_INST->txda(txda);
        ring_INST->rxda(rxda);
        ring_INST->txc(txc);
        ring_INST->outstrobe(outstrobe);

        SC_METHOD(reset_generator);
        sensitive << reset_deactivation_event;

        SC_METHOD(generate_data);
        sensitive << txc.posedge_event();
        sensitive << reset.negedge_event();
        dont_initialize();

        SC_METHOD(compare_data)
        sensitive << clock.negedge_event();
        dont_initialize();
        
        SC_METHOD(print_error);
        sensitive << dataerror.negedge_event();
        dont_initialize();
        
        SC_METHOD(print_restore);
        sensitive << dataerror.posedge_event();
        dont_initialize();
        
        SC_METHOD(clock_assign);
        sensitive << clock.signal();
        dont_initialize();
    }

    ~test_ringbuf()
    {
        delete ring_INST; ring_INST = 0;
    }
};

#endif
