// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_RINGBUF
#define INCLUDED_RINGBUF

#include <systemc.h>

class ringbuf : public sc_foreign_module
{
public:
    // Module ports
    sc_in<bool>                  clock;
    sc_in<bool>                  reset;
    sc_in<bool>                  txda;
    sc_out<bool>                 rxda;
    sc_out<bool>                 outstrobe;
    sc_out<bool>                 txc;

    ringbuf(sc_module_name nm)
        : sc_foreign_module(nm, "ringbuf"),
          clock("clock"),
          reset("reset"),
          txda("txda"),
          rxda("rxda"),
          outstrobe("outstrobe"),
          txc("txc")
    {
    }

    ~ringbuf()
    {
    }
};

#endif
