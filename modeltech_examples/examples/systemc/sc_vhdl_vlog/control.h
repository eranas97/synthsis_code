// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_CONTROL
#define INCLUDED_CONTROL

#include <systemc.h>

class control : public sc_foreign_module
{
public:
    sc_in<bool>               clock;
    sc_in<bool>               reset;
    sc_out<sc_uint<9> >       ramadrs;
    sc_out<bool>              oeenable;
    sc_out<bool>              txc;
    sc_out<bool>              outstrobe;

    // Constructor
    control(sc_module_name nm, const char* hdl_name)
        : sc_foreign_module(nm, hdl_name),
          clock("clock"),
          reset("reset"),
          ramadrs("ramadrs"),
          oeenable("oeenable"),
          txc("txc"),
          outstrobe("outstrobe")
    {}


    // Empty Destructor
    ~control()
    {
    }
};

#endif
