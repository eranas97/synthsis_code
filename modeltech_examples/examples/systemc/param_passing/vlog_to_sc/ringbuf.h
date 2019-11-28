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

SC_MODULE(ringbuf)
{
public:
    // Module ports
    sc_in<bool>                  clock;
    sc_in<bool>                  Reset;
    sc_in<bool>                  txda;
    sc_out<bool>                 rxda;
    sc_out<bool>                 outstrobe;
    sc_out<bool>                 txc;

    // Signals interconnecting child instances
    sc_signal<sc_uint<9> >       ramadrs;
    sc_signal<sc_uint<16> >      buffer;
    sc_signal<bool >             oeenable;

    // Child instances
    control*                     block1;
    store*                       block2;
    retrieve*                    block3;

    SC_CTOR(ringbuf)
        : clock("clock"),
          Reset("Reset"),
          txda("txda"),
          rxda("rxda"),
          outstrobe("outstrobe"),
          txc("txc"),
          ramadrs("ramadrs"),
          buffer("buffer"),
          oeenable("oeenable")
    {
        block1 = new control("block1");
        block1->clock(clock);
        block1->reset(Reset);
        block1->ramadrs(ramadrs);
        block1->txc(txc);
        block1->oeenable(oeenable);
        block1->outstrobe(outstrobe);

        block2 = new store("block2");
        block2->clock(clock);
        block2->reset(Reset);
        block2->oeenable(oeenable);
        block2->ramadrs(ramadrs);
        block2->buffer(buffer);
        block2->txda(txda);

        block3 = new retrieve("block3");
        block3->outstrobe(outstrobe);
        block3->ramadrs(ramadrs);
        block3->buffer(buffer);
        block3->rxda(rxda);

		int return_status = 0;

		int counter_size = 0;
		counter_size = sc_get_int_param("counter_size", &return_status);
		if (return_status)
			printf("counter_size=%d\n", counter_size);

		int buffer_size = 0;
		if (sc_get_param("buffer_size", buffer_size))
			printf("buffer_size=%d\n", buffer_size);

		double real_param = sc_get_real_param("real_param", &return_status);
		if (return_status)
			printf("real_param=%g\n", real_param);


		int exp1_param = sc_get_int_param("exp1_param", &return_status);
		if (return_status)
			printf("exp1_param=%d\n", exp1_param);

		int exp2_param = 0;
		if (sc_get_param("exp2_param", exp2_param))
			printf("exp2_param=%d\n", exp2_param);

		std::string str_param;
		if (sc_get_param("str_param", str_param, 'a'))
			printf("str_param=%s\n", str_param.c_str());


		std::string range_param = sc_get_string_param("range_param", 'b', &return_status);
		if (return_status)
			printf("range_param=%s\n", range_param.c_str());
		
    }

    ~ringbuf()
    {
        delete block1; block1 = 0;
        delete block2; block2 = 0;
        delete block3; block3 = 0;
    }
};

#endif
