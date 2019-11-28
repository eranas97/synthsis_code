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
    sc_clock clock;

    sc_event reset_deactivation_event;

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

    int counter;

    // module instances
    ringbuf* ring_INST;

    void reset_generator();
    void generate_data();
    void compare_data();
    void print_error(); // negedge data
    void print_restore();

    // Constructor
    SC_CTOR(test_ringbuf)
      : clock("clock", 10, SC_NS, 0.5, 0.0, SC_NS, false),
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
        const char* generic_list[2];
        generic_list[0] = "counter_size=4";
        generic_list[1] = "buffer_size=16";
        ring_INST = new ringbuf("ring_INST", "ringbuf", 2, generic_list);

        // Connect ports
        ring_INST->clock(clock);
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
        reset.write(0);
        reset_deactivation_event.notify(400, SC_NS);
    }
    else
        reset.write(1);
}


//
// Generates a pseudo-random data stream that is
// used as the input to the ring buffer.
// The process fires on the posedge of txc.
//
inline void test_ringbuf::generate_data()
{
    // Use a 20-bit LFSR to generate data
    if (reset.read() == 0)
    {
        // Reset pseudo-random data
        pseudo.write(0);
        txda.write(0);
    }
    else
    {
        sc_uint<20> var_pseudo = pseudo.read();
        sc_uint<20> var_pseudo_newval = (var_pseudo.range(18, 0), var_pseudo[2] ^ !var_pseudo[19]);
        pseudo.write(var_pseudo_newval);

        if (var_pseudo_newval[19] != var_pseudo[19])
            txda.write((bool)var_pseudo_newval[19]);
    }
}


//
// On every negedge of the clock, compare actual and expected data.
//
inline void test_ringbuf::compare_data()
{
    bool var_dataerror_newval = actual.read() ^ !expected.read();
    dataerror.write(var_dataerror_newval);

    if (reset.read() == 0)
    {
        storage.write(0);
        expected.write(0);
        actual.write(0);
        counter--;
    }
    else
    {
        if (outstrobe.read())
        {
            sc_uint<20> var_storage = storage.read();
            sc_uint<20> var_storage_newval = (var_storage.range(18, 0), rxda.read());
            storage.write(var_storage_newval);
            actual.write((bool)var_storage_newval[0]);
            counter++;

            expected.write(var_storage[2] ^ !var_storage[19]);
        }
    }
}


inline void test_ringbuf::print_error()
{
    cout << "\n** NOTICE  ** at " << sc_time_stamp() << ": Data value not expected.\n";
}


inline void test_ringbuf::print_restore()
{
    if (sc_time_stamp().to_default_time_units() > 1)
        cout << "\n** RESTORED ** at " << sc_time_stamp() << ": Data returned to expected value.\n";
}
