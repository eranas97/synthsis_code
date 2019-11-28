// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_RINGBUF
#define INCLUDED_RINGBUF

#include <systemc.h>
#include "control.h"
#include "store.h"
#include "retrieve.h"

//
// This sc_module has two parameters:
// 1. COUNT_SIZE is the counter size - can be 2, 3, 4, 5, ...
// 2. BUF_SIZE is the buffer size - can be 4, 8, 16, 32, ...
//
template <int COUNT_SIZE = 4, int BUF_SIZE = 16>
class ringbuf : public sc_module
{
public:
    // Module ports
    sc_in<bool>                  clock;
    sc_in<bool>                  reset;
    sc_in<bool>                  txda;
    sc_out<bool>                 rxda;
    sc_out<bool>                 outstrobe;
    sc_out<bool>                 txc;

    // Signals interconnecting child instances
    sc_signal<sc_uint<COUNT_SIZE*2+1> >  ramadrs;
    sc_signal<sc_uint<BUF_SIZE> >      buffer;
    sc_signal<bool >             oeenable;

    // Child instances
    control<COUNT_SIZE>*                 block1;
    store<COUNT_SIZE,BUF_SIZE>*                block2;
    retrieve<COUNT_SIZE,BUF_SIZE>*             block3;

    SC_CTOR(ringbuf)
        : clock("clock"),
          reset("reset"),
          txda("txda"),
          rxda("rxda"),
          outstrobe("outstrobe"),
          txc("txc"),
          ramadrs("ramadrs"),
          buffer("buffer"),
          oeenable("oeenable")
    {
        block1 = new control<COUNT_SIZE>("block1");
        block1->clock(clock);
        block1->reset(reset);
        block1->ramadrs(ramadrs);
        block1->txc(txc);
        block1->oeenable(oeenable);
        block1->outstrobe(outstrobe);

        block2 = new store<COUNT_SIZE,BUF_SIZE>("block2");
        block2->clock(clock);
        block2->reset(reset);
        block2->oeenable(oeenable);
        block2->ramadrs(ramadrs);
        block2->buffer(buffer);
        block2->txda(txda);

        block3 = new retrieve<COUNT_SIZE,BUF_SIZE>("block3");
        block3->outstrobe(outstrobe);
        block3->ramadrs(ramadrs);
        block3->buffer(buffer);
        block3->rxda(rxda);
    }

    ~ringbuf()
    {
        delete block1; block1 = 0;
        delete block2; block2 = 0;
        delete block3; block3 = 0;
    }
};

#endif
