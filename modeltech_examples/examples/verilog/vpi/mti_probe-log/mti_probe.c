/*
 * Copyright 1991-2016 Mentor Graphics Corporation
 * All Rights Reserved.
 * THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
 * PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
 * LICENSE TERMS.
 * VPI routine for logging of signals from within the HDL code
 */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "vpi_user.h"
#include "mti.h"

/*
 * Compiletf routine
 */
int Probe_Compile(char *user_data)
{
    s_vpi_value str_arg;
	int tfarg_num = 0;
	int tfarg_type;

	vpiHandle systf_h, arg_itr, arg_h;
	systf_h = vpi_handle(vpiSysTfCall, NULL);
	arg_itr = vpi_iterate(vpiArgument, systf_h);
	if (arg_itr == NULL) {
		vpi_printf("ERROR: $mti_probe requires at least 1 argument.\n");
		vpi_control(vpiFinish, 0);
	}
	else {
		while ((arg_h = vpi_scan(arg_itr))) {
			tfarg_num++;
		    tfarg_type = vpi_get(vpiType, arg_h);
		    switch (tfarg_type) {
		        case vpiModule:
			    case vpiNet:
			    case vpiReg:
			        break;
			    case vpiConstant:
			        str_arg.format = vpiStringVal;
			        vpi_get_value(arg_h, &str_arg);
		        	if ((strcmp(str_arg.value.str, "A") != 0) && (strcmp(str_arg.value.str, "AC") != 0) && (strcmp(str_arg.value.str, "C") != 0)) {
				        vpi_printf("ERROR: $mti_probe argument %d: ", tfarg_num);
				        vpi_printf("Argument string must be A, C, AC.\n");
				        vpi_control(vpiFinish, 0);
				    }
			        break;
			    default:
			        vpi_printf("ERROR: $mti_probe argument %d: ", tfarg_num);
			        vpi_printf("Argument must be a module, net, reg, or string.\n");
			        vpi_control(vpiFinish, 0);
		    }
		}
	}
	return(0);
}

int log_signals(vpiHandle, vpiHandle);

/*
 * Calltf routine
 */
int Probe_Call(char *user_data)
{
    vpiHandle systf_h, arg_itr, arg_h, scope_h;

    systf_h = vpi_handle(vpiSysTfCall, NULL);
    scope_h = vpi_handle(vpiScope, systf_h);
    arg_itr = vpi_iterate(vpiArgument, systf_h);

    while ((arg_h = vpi_scan(arg_itr))) {
        log_signals(arg_h, scope_h);
    }
    return(0);
}

/*
 * Function for logging signals
 */
int log_signals(vpiHandle arg_h, vpiHandle scope_h)
{
    s_vpi_value str_arg;
	char log_path[256];
    int tfarg_type;

	tfarg_type = vpi_get(vpiType, arg_h);

    switch (tfarg_type) {
	    case vpiModule:
		    vpi_printf("NOTE: Logging signals in instance:\t\t %s\n", vpi_get_str(vpiFullName, arg_h));
			sprintf(log_path, "log %s.*", vpi_get_str(vpiFullName, arg_h));
	        break;
		case vpiNet:
			vpi_printf("NOTE: Logging net:\t\t\t\t %s\n", vpi_get_str(vpiFullName, arg_h));
			sprintf(log_path, "log %s", vpi_get_str(vpiFullName, arg_h));
		    break;
	    case vpiReg:
			vpi_printf("NOTE: Logging register:\t\t\t %s\n", vpi_get_str(vpiFullName, arg_h));
			sprintf(log_path, "log %s", vpi_get_str(vpiFullName, arg_h));
			break;
		case vpiConstant:
			str_arg.format = vpiStringVal;
			vpi_get_value(arg_h, &str_arg);
			if (strcmp(str_arg.value.str, "A") == 0) {
			    /* Log ALL nodes in current scope */
	            vpi_printf("NOTE: Logging current scope - all nodes:\t %s\n", vpi_get_str(vpiFullName, scope_h));
	            sprintf(log_path, "log %s.*", vpi_get_str(vpiFullName, scope_h));
			}
			else if (strcmp(str_arg.value.str, "AC") == 0) {
				/* Log ALL nodes recursively starting in the current scope */
				vpi_printf("NOTE: Logging current scope - recursively:\t %s\n", vpi_get_str(vpiFullName, scope_h));
				sprintf(log_path, "log -r %s.*", vpi_get_str(vpiFullName, scope_h));
			}
			else if (strcmp(str_arg.value.str, "C") == 0) {
				/* Log ONLY ports recursively starting in the current scopes */
			    vpi_printf("NOTE: Logging current scope - ports only:\t %s\n", vpi_get_str(vpiFullName, scope_h));
				sprintf(log_path, "log -ports -r %s.*", vpi_get_str(vpiFullName, scope_h));
			}
	}
	mti_Command(log_path);
	return(0);
}

/*
 * $mti_probe VPI registration function
 */
void Probe_Register()
{
	s_vpi_systf_data systf_data;
	systf_data.type         = vpiSysTask;
	systf_data.sysfunctype  = 0;
	systf_data.tfname       = "$mti_probe";
	systf_data.calltf       = Probe_Call;
	systf_data.compiletf    = Probe_Compile;
	systf_data.sizetf       = NULL;
	systf_data.user_data    = NULL;
	vpi_register_systf(&systf_data);
}
