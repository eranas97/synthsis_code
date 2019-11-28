/******************************************************************************
 *  UCDB API User Guide Example
 *
 *  Copyright 2016 Mentor Graphics Corporation
 *
 *  All Rights Reserved.
 *
 *  THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
 *  PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
 *  LICENSE TERMS.
 *
 *  Usage: <program> ucdbfile
 *
 *  UCDB API User Guide Example.
 *
 *  Traverse all scopes in a UCDB in READ STREAMING.
 *
 *****************************************************************************/
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>

ucdbCBReturnT
callback(
    void*           userdata,
    ucdbCBDataT*    cbdata)
{
    ucdbScopeT scope;
    switch (cbdata->reason) {
    case UCDB_REASON_DU:
    case UCDB_REASON_SCOPE:
        scope = (ucdbScopeT)(cbdata->obj);
        printf("%s\n",ucdb_GetScopeHierName(cbdata->db,scope));
        break;
    default: break;
    }
    return UCDB_SCAN_CONTINUE;
}

void
example_code(const char* ucdbfile)
{
	ucdb_OpenReadStream(ucdbfile,callback,NULL);
}

void
error_handler(void *data,
              ucdbErrorT *errorInfo)
{
    fprintf(stderr, "UCDB Error: %s\n", errorInfo->msgstr);
    if (errorInfo->severity == UCDB_MSG_ERROR)
        exit(1);
}

int
main(int argc, char* argv[])
{
    if (argc<2) {
        printf("Usage:   %s <ucdb file name>\n",argv[0]);
        printf("Purpose: Traverse all scopes in a UCDB in READ STREAMING.\n");
        return 1;
    }
    ucdb_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1]);
    return 0;
}
