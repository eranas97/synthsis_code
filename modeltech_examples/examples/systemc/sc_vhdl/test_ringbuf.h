// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// test_ringbuf.h

#ifndef INCLUDED_TESTRING
#define INCLUDED_TESTRING

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

    int counter;

    // module instances
    ringbuf* ring_INST;

    void reset_generator();
    void generate_data();
    void compare_data();
    void print_error(); // negedge_event data
    void print_restore();
    void clock_assign();

    // Constructor
    SC_CTOR(test_ringbuf)
      : clock("clock", 200, SC_NS, 0.5, 0.0, SC_NS, false),
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
        actual("actual"),
        counter( 0 )
    {
        // Create instances
        ring_INST = new ringbuf("ring_INST", "work.ringbuf");

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
        sensitive << clock.posedge_event();
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


//
// Reset pulse generator.
// The first time it runs at initialization and sets reset low.
// It schedules a wakeup at time 400 ns, and at that time sets
// reset high (inactive).
//
inline void test_ringbuf::reset_generator()
{
    static bool first = true;
    if (first)
    {
        first = false;
        reset.write(SC_LOGIC_0);
        reset_deactivation_event.notify(400, SC_NS);
    }
    else
        reset.write(SC_LOGIC_1);
}


//
// Generates a pseudo-random data stream that is
// used as the input to the ring buffer.
// The process fires on the posedge_event of txc.
//
inline void test_ringbuf::generate_data()
{
    // Use a 20-bit LFSR to generate data
    if (reset.read() == 0)
    {
        // Reset pseudo-random data
        pseudo.write(0);
        txda.write(SC_LOGIC_0);
    }
    else
    {
        sc_lv<20> var_pseudo = pseudo.read();
        sc_lv<20> var_pseudo_newval = (var_pseudo.range(18, 0), var_pseudo[2] ^ ~var_pseudo[19]);
        pseudo.write(var_pseudo_newval);

        if (var_pseudo_newval[19] != var_pseudo[19])
            txda.write(var_pseudo_newval[19]);
    }
}


//
// On every negedge_event of the clock, compare actual and expected data.
//
inline void test_ringbuf::compare_data()
{
    sc_logic var_dataerror_newval = actual.read() ^ ~expected.read();
    dataerror.write(var_dataerror_newval);

    if (reset.read() == SC_LOGIC_0)
    {
        storage.write(0);
        expected.write(SC_LOGIC_0);
        actual.write(SC_LOGIC_0);
        counter--;
    }
    else
    {
        if (outstrobe.read() == SC_LOGIC_1)
        {
            sc_lv<20> var_storage = storage.read();
            sc_lv<20> var_storage_newval = (var_storage.range(18, 0), rxda.read());
            storage.write(var_storage_newval);
            actual.write(var_storage_newval[0]);
            counter++;

            expected.write(var_storage[2] ^ ~var_storage[19]);
        }
    }
}


inline void test_ringbuf::print_error()
{
    cout << "\n** NOTICE  ** at " << sc_time_stamp() << ": Data value not expected.\n" << flush;
}


inline void test_ringbuf::print_restore()
{
    if (sc_time_stamp().to_default_time_units() > 600)
        cout << "\n** RESTORED ** at " << sc_time_stamp() << ": Data returned to expected value.\n" << flush;
}


inline void test_ringbuf::clock_assign()
{
    sc_logic clock_tmp(clock.signal().read());
    iclock.write(clock_tmp);
}
#endif
