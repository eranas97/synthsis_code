// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_RETRIEVE
#define INCLUDED_RETRIEVE

#include <systemc.h>

//
// This sc_module has two parameters:
// 1. COUNT_SIZE is the counter size - can be 2, 3, 4, 5, ...
// 2. BUF_SIZE is the buffer size - can be 4, 8, 16, 32, ...
//
template <int COUNT_SIZE = 4, int BUF_SIZE = 16>
class retrieve : public sc_module
{
public:
    // Ports
    sc_in<bool>              outstrobe;
    sc_in<sc_uint<COUNT_SIZE*2+1> >  ramadrs;
    sc_in<sc_uint<BUF_SIZE> >      buffer;
    sc_out<bool>             rxda;

    // Internal Signals
    sc_signal<bool>          rd0a;

    // Methods
    void retriever();
    void rxda_driver();

    SC_CTOR(retrieve)
        : outstrobe("outstrobe"),
          ramadrs("ramadrs"),
          buffer("buffer"),
          rxda("rxda"),
          rd0a("rd0a")
    {
        SC_METHOD(retriever);
        sensitive << buffer << ramadrs;
        dont_initialize();

        SC_METHOD(rxda_driver);
        sensitive << rd0a << outstrobe;
        dont_initialize();
    }

    // Destructor does nothing
    ~retrieve()
    {
    }
};


//
// This method assigns temporary signal rd0a to the
// properly selected bit in the buffer.
//
template <int COUNT_SIZE, int BUF_SIZE>
void retrieve<COUNT_SIZE,BUF_SIZE>::retriever()
{
    int i = ramadrs.read().range(COUNT_SIZE-1, 0);
    rd0a.write((bool)buffer.read()[i]);
}


//
// This method drives the rxda signal
//
template <int COUNT_SIZE, int BUF_SIZE>
void retrieve<COUNT_SIZE,BUF_SIZE>::rxda_driver()
{
    rxda.write(rd0a.read() && outstrobe.read());
}

#endif
