/*
 * Copyright 1991-2016 Mentor Graphics Corporation
 *
 * All Rights Reserved.
 *
 * THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
 * PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
 * LICENSE TERMS.
 *
 * Simple SystemVerilog DPI Example - Using VPI and DPI together
 */
#include "vpi_user.h"
#include "dpi_vpi.h"

vpiHandle VPI_handle_by_name(const char *name) {
    vpiHandle handle = vpi_handle_by_name((char*)name, 0);
    if (handle != NULL) {
        return handle;
    } else {
        vpi_printf("VPI_handle_by_name: Can't find name %s\n", name);
        return 0;
    }
}

int32_t VPI_get_value(vpiHandle handle) {
    s_vpi_value value_p;
    if (handle) {
        value_p.format = vpiIntVal;
        vpi_get_value(handle, &value_p);
        return value_p.value.integer;
    }
    else {
        vpi_printf("VPI_get_value: error null handle\n");
        return 0;
    }
}

void VPI_put_value(vpiHandle handle, int value) {
    s_vpi_value value_p;
    if (handle) {
        value_p.format = vpiIntVal;
        value_p.value.integer = value;
        vpi_put_value(handle, &value_p, 0, vpiNoDelay);
    }
    else {
        vpi_printf("VPI_put_value: error null handle\n");
    }
}
