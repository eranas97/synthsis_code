/*
 * Copyright 1991-2016 Mentor Graphics Corporation
 * All Rights Reserved.
 * THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
 * PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
 * LICENSE TERMS.
 * VPI routine for logging of signals from within the HDL code
 */
extern void Probe_Register();

void (*vlog_startup_routines[])() =
{
    Probe_Register,          /* mti_probe systf registration function */
    0                        /* final entry must be 0 */
};
