// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#include "test_ringbuf.h"

SC_MODULE(top)
{
    test_ringbuf test;

    SC_CTOR(top)
        : test("test")
    {}
};
