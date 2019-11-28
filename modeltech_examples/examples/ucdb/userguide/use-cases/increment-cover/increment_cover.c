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
 *  Increment the given coveritem in a UCDB.
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
    switch (cbdata->reason) {
    case UCDB_REASON_CVBIN:
        ucdb_IncrementCover(cbdata->db,(ucdbScopeT)(cbdata->obj),
                            cbdata->coverindex,1);
        return UCDB_SCAN_STOP;
        break;
    default: break;
    }
    return UCDB_SCAN_CONTINUE;
}

void
example_code(const char* ucdbfile, const char* path)
{
    ucdbT db = ucdb_Open(ucdbfile);
    if (db==NULL)
        return;
    ucdb_PathCallBack(db,
                      0,    /* don't recurse from found object */
                      path,
                      NULL, /* design unit name does not apply */
                      UCDB_NONTESTPLAN_SCOPE,   /* tree root type */
                      -1,   /* match any scope type */
                      -1,   /* match any coveritem type */
                      callback, NULL);
    ucdb_Write(db,ucdbfile,
               NULL,    /* save entire database */
               1,       /* recurse: not necessary with NULL */
               -1);     /* save all scope types */
    ucdb_Close(db);
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
    if (argc<3) {
        printf("Usage:   %s <ucdb file name> <path to cover>\n",argv[0]);
        printf("Purpose: Increment the given coveritem in a UCDB.\n");
        return 1;
    }
    ucdb_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1],argv[2]);
    return 0;
}

