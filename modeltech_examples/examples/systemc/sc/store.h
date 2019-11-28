// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_STORE
#define INCLUDED_STORE


#include <systemc.h>

//
// This sc_module has two parameters:
// 1. COUNT_SIZE is the counter size - can be 2, 3, 4, 5, ...
// 2. BUF_SIZE is the buffer size - can be 4, 8, 16, 32, ...
//
template <int COUNT_SIZE = 4, int BUF_SIZE = 16>
class store : public sc_module
{
public:
    sc_in<bool>              clock;
    sc_in<bool>              reset;
    sc_in<bool>              oeenable;
    sc_in<bool>              txda;
    sc_in<sc_uint<COUNT_SIZE*2+1> >  ramadrs;
    sc_out<sc_uint<BUF_SIZE> >     buffer;

    void storer();

    SC_CTOR(store)
        : clock("clock"),
          reset("reset"),
          oeenable("oeenable"),
          txda("txda"),
          ramadrs("ramadrs"),
          buffer("buffer")
    {
        SC_METHOD(storer);
        sensitive << clock.pos();
        dont_initialize();
    }

    // Destructor does nothing
    ~store()
    {
    }
};


//
// This process initializes the buffer.
// In operation, it uses the ramadrs input to
// select the appropriate bit and set it to
// the value of txda.
//
template <int COUNT_SIZE, int BUF_SIZE>
void store<COUNT_SIZE,BUF_SIZE>::storer()
{
    if (reset.read() == 0)
        buffer.write(0);
    else if (oeenable.read() == 0)
    {
        // Calculate address of bit in buffer that we should write.
        int i = ramadrs.read().range(COUNT_SIZE*2, COUNT_SIZE+1);

        // RMW operation - merge in the txda bit.
        sc_uint<BUF_SIZE> var_buffer = buffer.read();
        var_buffer[i] = txda;
        buffer.write(var_buffer);
    }
}

#endif
