/*
 * Copyright 1991-2016 Mentor Graphics Corporation
 *
 * All Rights Reserved.
 *
 * THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
 * PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
 * LICENSE TERMS.
 *
 * Simple SystemVerilog DPI Example - C model 8-to-1 multiplexer
 */
#include "mux81.h"

int mux81 (
    int select,
    int i0,
    int i1,
    int i2,
    int i3,
    int i4,
    int i5,
    int i6,
    int i7)
{
    switch (select) {
        case 0x0: return(i0);
        case 0x1: return(i1);
        case 0x2: return(i2);
        case 0x3: return(i3);
        case 0x4: return(i4);
        case 0x5: return(i5);
        case 0x6: return(i6);
        case 0x7: return(i7);
    }
    return 0;
}
