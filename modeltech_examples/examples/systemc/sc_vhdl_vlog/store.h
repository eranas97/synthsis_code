// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_STORE
#define INCLUDED_STORE


#include <systemc.h>

class store : public sc_foreign_module
{
public:
    sc_in<bool>              clock;
    sc_in<bool>              reset;
    sc_in<bool>              oeenable;
    sc_in<bool>              txda;
    sc_in<sc_uint<9> >       ramadrs;
    sc_out<sc_uint<16> >     buffer;

    store(sc_module_name nm, const char* hdl_name)
        : sc_foreign_module(nm, hdl_name),
          clock("clock"),
          reset("reset"),
          oeenable("oeenable"),
          txda("txda"),
          ramadrs("ramadrs"),
          buffer("buffer")
    {}

    // Destructor does nothing
    ~store()
    {}
};

#endif
