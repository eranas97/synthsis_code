#include <stdlib.h>
#include <stdio.h>
#include "vpi_user.h"


int adderSizetf(char* user_data)
{
    return 32;
}


int adderCalltf(char* user_data)
{
    s_vpi_value value_s;
    vpiHandle   systf_handle, arg_itr, arg_handle;
    int         operand1, operand2, result;

    systf_handle = vpi_handle(vpiSysTfCall, NULL);
    arg_itr = vpi_iterate(vpiArgument, systf_handle);
    if (arg_itr == NULL) {
        vpi_printf("ERROR: $add failed to obtain systf arg handles\n");
        return 0;
    }

    /* read operand 1 from systf arg 1 */
    arg_handle = vpi_scan(arg_itr);
    value_s.format = vpiIntVal;
    vpi_get_value(arg_handle, &value_s);
    operand1 = value_s.value.integer;
    vpi_free_object(arg_handle);

    /* read operand 2 from systf arg 2 */
    arg_handle = vpi_scan(arg_itr);
    vpi_get_value(arg_handle, &value_s);
    operand2 = value_s.value.integer;
    vpi_free_object(arg_handle);

    /* calculate the sum */
    result = operand1 + operand2;

    /* write result to simulation as return value $adder */
    value_s.value.integer = result;
    vpi_put_value(systf_handle, &value_s, NULL, vpiNoDelay);

    vpi_free_object(arg_itr);
    vpi_free_object(systf_handle);
    return 0;
}


void adder_register()
{
    s_vpi_systf_data tf_data;

    tf_data.type        = vpiSysFunc;
    tf_data.sysfunctype = vpiSysFuncSized;
    tf_data.tfname      = "$add";
    tf_data.calltf      = adderCalltf;
    tf_data.compiletf   = NULL;
    tf_data.sizetf      = adderSizetf;
    vpi_register_systf(&tf_data);
}


void (*vlog_startup_routines[])() = 
{
    /*** add user entries here ***/
    adder_register,
    0 /*** final entry must be 0 ***/
};
