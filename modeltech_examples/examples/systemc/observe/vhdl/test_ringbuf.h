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
    // Clock period set to 5MHz
    sc_clock clock;

    sc_event reset_deactivation_event;

    sc_signal<sc_logic>          iclock;
    sc_signal<sc_logic>          reset;
    sc_signal_resolved           txda;
    sc_signal_resolved           rxda;
    sc_signal<sc_logic>          txc;
    sc_signal<sc_logic>          outstrobe;
    sc_signal_rv<16>             buffers;

    sc_signal<sc_lv<20> >        pseudo;
    sc_signal<sc_lv<20> >        storage;
    sc_signal<sc_logic>          expected;
    sc_signal<sc_logic>          dataerror;
    sc_signal<sc_logic>          actual;

    // module instances
    ringbuf* ring_INST;

    const char* generic_list[2];

    // observe vhdl signals
    sc_signal<bool>      sig1;
    sc_signal<bool>      sig2;
    sc_signal<sc_lv<4> > sig3;
    sc_signal<sc_logic>  sig4;

    void reset_generator();
    void generate_data();
    void compare_data();
    void print_error(); // negedge data
    void print_restore();
    void clock_assign();
    void print_sig1();
    void print_sig2();
    void print_sig3();
    void print_sig4();

    // Constructor
    SC_CTOR(test_ringbuf)
	  : clock("clock", 200, SC_NS, 0.5, 0.0, SC_NS, false),
        iclock("iclock"),
        reset("reset"),
        txda("txda"),
        rxda("rxda"),
        txc("txc"),
        outstrobe("outstrobe"),
        buffers("buffers"),
        pseudo("pseudo"),
        storage("storage"),
        expected("expected"),
        dataerror("dataerror"),
        actual("actual")
    {
        generic_list[0] = "counter_size=4";
        generic_list[1] = "buffer_size=16";

        // Create instances
        ring_INST = new ringbuf("ring_INST", "ringbuf", 2, generic_list);

        // Connect ports
        ring_INST->clock(iclock);
        ring_INST->reset(reset);
        ring_INST->txda(txda);
        ring_INST->rxda(rxda);
        ring_INST->txc(txc);
        ring_INST->outstrobe(outstrobe);
        ring_INST->buffers(buffers);

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
        sensitive << dataerror;
        dont_initialize();

        SC_METHOD(print_restore);
        sensitive << dataerror;
        dont_initialize();

        SC_METHOD(clock_assign);
        sensitive << clock.signal();
        dont_initialize();

        SC_METHOD(print_sig1);
        sensitive << sig1;

        SC_METHOD(print_sig2);
        sensitive << sig2;

        SC_METHOD(print_sig3);
        sensitive << sig3;

        SC_METHOD(print_sig4);
        sensitive << sig4;

        sig1.observe_foreign_signal("/test_ringbuf/ring_INST/block1_INST/sig1");
        sig2.observe_foreign_signal("/test_ringbuf/ring_INST/block1_INST/sig2");
        sig3.observe_foreign_signal("/test_ringbuf/ring_INST/block1_INST/sig3");
        sig4.observe_foreign_signal("/test_ringbuf/ring_INST/block1_INST/sig4(0)");
    }

    ~test_ringbuf()
    {
        delete ring_INST; ring_INST = 0;
    }
};
