// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_RETRIEVE
#define INCLUDED_RETRIEVE


#include <systemc.h>

class retrieve : public sc_foreign_module
{
public:
    // Ports
    sc_in<bool>              outstrobe;
    sc_in<sc_uint<9> >       ramadrs;
    sc_in<sc_uint<16> >      buffer;
    sc_out<bool>             rxda;

    // Internal Signals
    sc_signal<bool>          rd0a;

    retrieve(sc_module_name nm, const char* hdl_name)
        : sc_foreign_module(nm, hdl_name),
          outstrobe("outstrobe"),
          ramadrs("ramadrs"),
          buffer("buffer"),
          rxda("rxda"),
          rd0a("rd0a")
    {}

    // Destructor does nothing
    ~retrieve()
    {
    }
};

#endif
