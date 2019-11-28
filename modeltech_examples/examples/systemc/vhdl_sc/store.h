// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_STORE
#define INCLUDED_STORE

#include <systemc.h>

SC_MODULE(store)
{
public:
    sc_in<sc_logic>        clock;
    sc_in<sc_logic>        reset;
    sc_in<sc_logic>        oeenable;
    sc_in<sc_logic>        txda;
    sc_in<sc_lv<9> >       ramadrs;
    sc_out<sc_lv<16> >     buffer;

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
inline void store::storer()
{
    if (reset.read() == SC_LOGIC_0)
        buffer.write(0);
    else if (oeenable.read() == SC_LOGIC_0)
    {
        // Calculate address of bit in buffer that we should write.
        int i = ramadrs.read().range(8, 5).get_word(0);

        // RMW operation - merge in the txda bit.
        sc_lv<16> var_buffer = buffer.read();
        var_buffer[i] = txda;
        buffer.write(var_buffer);
    }
}

#endif
