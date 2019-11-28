/*
 * Copyright 1991-2016 Mentor Graphics Corporation
 *
 * All Rights Reserved.
 *
 * THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
 * PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
 * LICENSE TERMS.
 *
 * Simple SystemVerilog DPI Example - C function to compute fibonacci seq.
 */
#include "fibonacci.h"

unsigned int fibonacci(unsigned int N)
{
    unsigned int a = 1, b = 1;
    unsigned int c, i;

    for (i = 3; i <= N; i++) {
        c = a + b;
        a = b;
        b = c;
    }           
    return b;
}
