// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#include "main.h"

#ifdef MTI_SYSTEMC
SC_MODULE_EXPORT(top);
#else
int sc_main(int argc, char* argv[])
{
    test_ringbuf test("test");
    sc_start(500000, SC_NS);
    return 0;
}
#endif
