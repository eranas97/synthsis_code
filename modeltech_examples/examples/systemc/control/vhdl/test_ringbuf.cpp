// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

// test_ringbuf.cpp

#include "test_ringbuf.h"
#include <iostream>


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
        reset.write(SC_LOGIC_0);
        reset_deactivation_event.notify(400, SC_NS);
    }
    else
        reset.write(SC_LOGIC_1);
}


void test_ringbuf::set_control_signal()
{
    while (1) {
        sig1.write(true);
        sig2.write(SC_LOGIC_1);
        sig3.write("0101");
        sig4.write(false);
        cout << "SC drives sig1=true, sig2=1, sig3=0101, sig4(1)=false"
             << endl << flush;
        wait();
        sig1.write(false);
        sig2.write(SC_LOGIC_X);
        sig3.write("1111");
        sig4.write(true);
        cout << "SC drives sig1=false, sig2=X, sig3=1111, sig4(1)=true"
             << endl << flush;
        wait();
        sig1.write(true);
        sig2.write(SC_LOGIC_Z);
        sig3.write("0000");
        sig4.write(false);
        cout << "SC drives sig1=true, sig2=Z, sig3=0000, sig4(1)=false"
             << endl << flush;
        wait();
    }
}


//
// Generates a pseudo-random data stream that is
// used as the input to the ring buffers.
// The process fires on the posedge of txc.
//
void test_ringbuf::generate_data()
{
    // Generate a HiZ value for use later... (There's gotta be a betterw way)
    static int first = 1;
    static sc_lv<16> hiz_value;
    if (first)
    {
        first = 0;
        for (int i = 0; i < 16; i++)
            hiz_value[i] = SC_LOGIC_Z;
    }

    // Use a 20-bit LFSR to generate data
    if (reset.read() == 0)
    {
        // Reset pseudo-random data
        pseudo.write(0);
        txda.write(SC_LOGIC_0);
        // Write some weird value into buffer at reset time.
        buffers.write(0x1234);
    }
    else
    {
        sc_lv<20> var_pseudo = pseudo.read();
        sc_lv<20> var_pseudo_newval = (var_pseudo.range(18, 0), var_pseudo[2] ^ ~var_pseudo[19]);
        pseudo.write(var_pseudo_newval);

        if (var_pseudo_newval[19] != var_pseudo[19])
            txda.write(var_pseudo_newval[19]);

        // Muck with buffer every now and then - this fouls up the results
        if (var_pseudo[18] == SC_LOGIC_1 && var_pseudo[17] == SC_LOGIC_1) {
            buffers.write(0x1234);
        } else {
            buffers.write(hiz_value);
        }
    }
}


//
// On every negedge of the clock, compare actual and expected data.
//
void test_ringbuf::compare_data()
{
    sc_logic var_dataerror_newval = actual.read() ^ ~expected.read();
    dataerror.write(var_dataerror_newval);

    if (reset.read() == SC_LOGIC_0)
    {
        storage.write(0);
        expected.write(SC_LOGIC_0);
        actual.write(SC_LOGIC_0);
        rxda.write(SC_LOGIC_Z);
    }
    else
    {
        if (outstrobe.read() == SC_LOGIC_1)
        {
            sc_lv<20> var_storage = storage.read();
            sc_lv<20> var_storage_newval = (var_storage.range(18, 0), rxda.read());
            storage.write(var_storage_newval);
            actual.write(var_storage_newval[0]);

            expected.write(var_storage[2] ^ ~var_storage[19]);
        }
    }
}


void test_ringbuf::print_error()
{
    static sc_logic last_dataerror_val = SC_LOGIC_Z;
    //
    // DOUG 06/29/03
    // Need to make this process sensitive to both edges of the clock,
    // then screen for falling edge.  This is because in SystemC,
    // a 1->X transition apparently is not considered a "negedge".
    // A following transitions are considered a falling edge:
    // 1 -> X, X -> 0, 1 -> 0
    //
    if ((last_dataerror_val == SC_LOGIC_1 || last_dataerror_val == SC_LOGIC_X) &&
        (dataerror == SC_LOGIC_0 || dataerror == SC_LOGIC_X)) {

        cout << "\n** NOTICE  ** at "
             << sc_time_stamp()
             << ": Data value not expected.\n" << flush;
    }

    last_dataerror_val = dataerror.read();
}


void test_ringbuf::print_restore()
{
    static sc_logic last_dataerror_val = SC_LOGIC_Z;
    //
    // Need to make this process sensitive to both edges of the clock,
    // then screen for rising edge.  This is because in SystemC,
    // a 0->X transition apparently is not considered a "posedge".
    // A following transitions are considered a rising edge:
    // 0 -> X, X -> 1, 0 -> 1
    //
    if ((last_dataerror_val == SC_LOGIC_0 || last_dataerror_val == SC_LOGIC_X)  &&
        (dataerror == SC_LOGIC_1 || dataerror == SC_LOGIC_X)) {
        if (sc_time_stamp().to_default_time_units() > 600) {
            cout
                << "\n** RESTORED ** at "
                << sc_time_stamp()
                << ": Data returned to expected value.\n" << flush;
        }
    }
    last_dataerror_val = dataerror.read();
}


void test_ringbuf::clock_assign()
{
    sc_logic clock_tmp(clock.signal().read());
    iclock.write(clock_tmp);
}


#ifdef MTI_SYSTEMC
SC_MODULE_EXPORT(test_ringbuf);
#else
int
sc_main(int, char*[] )
{
    test_ringbuf top("top");
    sc_trace_file* tfile = sc_create_vcd_trace_file("test_ringbuf");
    sc_trace(tfile, top.clock, "clock");
    sc_trace(tfile, top.iclock, "iclock");
    sc_trace(tfile, top.reset, "reset");
    sc_trace(tfile, top.txda, "txda");
    sc_trace(tfile, top.rxda, "rxda");
    sc_trace(tfile, top.txc, "txc");
    sc_trace(tfile, top.outstrobe, "outstrobe");
    sc_trace(tfile, top.buffers, "buffers");
    sc_trace(tfile, top.pseudo, "pseudo");
    sc_trace(tfile, top.storage, "storage");
    sc_trace(tfile, top.expected, "expected");
    sc_trace(tfile, top.dataerror, "dataerror");
    sc_trace(tfile, top.actual, "actual");
    sc_start(500000, SC_NS);
    sc_close_vcd_trace_file(tfile);
}
#endif
