// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// test_ringbuf.cpp

#include "test_ringbuf.h"
#include <iostream>


SC_MODULE_EXPORT(test_ringbuf);


//
// Reset pulse generator.
// The first time it runs at initialization and sets reset low.
// It schedules a wakeup at time 400 ns, and at that time sets
// reset high (inactive).
//
void test_ringbuf::reset_generator()
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


void test_ringbuf::set_control_signal()
{
    while (1) {
        sig1.write(true);
        sig2.write(SC_LOGIC_1);
        sig3.write("0101");
        sig4.write(false);
        cout << "SC drives sig1=true, sig2=1, sig3=0101, sig4(0)=false" << endl << flush;
        wait();
        sig1.write(false);
        sig2.write(SC_LOGIC_X);
        sig3.write("1111");
        sig4.write(true);
        cout << "SC drives sig1=false, sig2=X, sig3=1111, sig4(0)=true" << endl << flush;
        wait();
        sig1.write(true);
        sig2.write(SC_LOGIC_Z);
        sig3.write("0000");
        sig4.write(false);
        cout << "SC drives sig1=true, sig2=Z, sig3=0000, sig4(0)=false" << endl << flush;
        wait();
    }
}


//
// Generates a pseudo-random data stream that is
// used as the input to the ring buffer.
// The process fires on the posedge of txc.
//
void test_ringbuf::generate_data()
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
            txda.write(var_pseudo_newval[19]);
    }
}


//
// On every negedge of the clock, compare actual and expected data.
//
void test_ringbuf::compare_data()
{
    bool var_dataerror_newval = actual.read() ^ !expected.read();
    dataerror.write(var_dataerror_newval);

    if (reset.read() == 0)
    {
        storage.write(0);
        expected.write(0);
        actual.write(0);
    }
    else
    {
        if (outstrobe.read())
        {
            sc_uint<20> var_storage = storage.read();
            sc_uint<20> var_storage_newval = (var_storage.range(18, 0), rxda.read());
            storage.write(var_storage_newval);
            actual.write(var_storage_newval[0]);

            expected.write(var_storage[2] ^ !var_storage[19]);
        }
    }
}


void test_ringbuf::print_error()
{
    cout << "\n** NOTICE  ** at " << sc_time_stamp() << ": Data value not expected.\n" << flush;
}


void test_ringbuf::print_restore()
{
    if (sc_time_stamp().to_default_time_units() > 1)
        cout << "\n** RESTORED ** at " << sc_time_stamp() << ": Data returned to expected value.\n" << flush;
}
