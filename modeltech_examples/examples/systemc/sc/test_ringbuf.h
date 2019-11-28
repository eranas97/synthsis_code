// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_TEST_RINGBUF
#define INCLUDED_TEST_RINGBUF

#include <systemc.h>

#include "ringbuf.h"

SC_MODULE(test_ringbuf)
{
    sc_event clock_event;
    sc_event reset_deactivation_event;

    sc_signal<bool> clock;
    sc_signal<bool> reset;
    sc_signal<bool> txda;
    sc_signal<bool> rxda;
    sc_signal<bool> txc;
    sc_signal<bool> outstrobe;

    sc_signal<sc_uint<20> > pseudo;
    sc_signal<sc_uint<20> > storage;
    sc_signal<bool> expected;
    sc_signal<bool> dataerror;
    sc_signal<bool> actual;

    // module instances
    ringbuf<>* ring_INST;

    void clock_generator();
    void reset_generator();
    void generate_data();
    void compare_data();
    void print_error(); // negedge data
    void print_restore();

    // Constructor
    SC_CTOR(test_ringbuf)
      : clock("clock"),
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
        ring_INST = new ringbuf<>("ring_INST");

        // Connect ports
        ring_INST->clock(clock);
        ring_INST->reset(reset);
        ring_INST->txda(txda);
        ring_INST->rxda(rxda);
        ring_INST->txc(txc);
        ring_INST->outstrobe(outstrobe);

        SC_METHOD(clock_generator);
        sensitive << clock_event;

        SC_METHOD(reset_generator);
        sensitive << reset_deactivation_event;

        SC_METHOD(generate_data);
        sensitive << txc.posedge_event();
        sensitive << reset.negedge_event();
        dont_initialize();

        SC_METHOD(compare_data)
        sensitive << clock.negedge_event();

        SC_METHOD(print_error);
        sensitive << dataerror.negedge_event();
        dont_initialize();

        SC_METHOD(print_restore);
        sensitive << dataerror.posedge_event();
        dont_initialize();
    }

    ~test_ringbuf()
    {
        delete ring_INST; ring_INST = 0;
    }
};

#endif
