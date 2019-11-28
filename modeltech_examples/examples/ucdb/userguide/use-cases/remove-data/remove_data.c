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
 *  Remove the named objects in a UCDB.
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
    int rc;
    ucdbScopeT scope = (ucdbScopeT)(cbdata->obj);
    ucdbT db = cbdata->db;
    char* name;
    switch (cbdata->reason) {
    case UCDB_REASON_SCOPE:
        printf("Removing scope %s\n",ucdb_GetScopeHierName(db,scope));
        ucdb_RemoveScope(db,scope);
        return UCDB_SCAN_PRUNE;
    case UCDB_REASON_CVBIN:
        ucdb_GetCoverData(db,scope,cbdata->coverindex,&name,NULL,NULL);
        printf("Removing cover %s/%s\n",ucdb_GetScopeHierName(db,scope),name);
        rc = ucdb_RemoveCover(db,scope,cbdata->coverindex);
        if (rc!=0) {
            printf("Unable to remove cover %s/%s\n",
                   ucdb_GetScopeHierName(db,scope), name);
        }
        break;
    default: break;
    }
    return UCDB_SCAN_CONTINUE;
}

void
example_code(const char* ucdbfile, const char* path)
{
    ucdbT db = ucdb_Open(ucdbfile);
    int matches;
    if (db==NULL)
        return;
    matches = ucdb_PathCallBack(db,
                                0,    /* don't recurse from found object */
                                path,
                                NULL, /* design unit name does not apply */
                                UCDB_NONTESTPLAN_SCOPE,   /* tree root type */
                                -1,   /* match any scope type */
                                -1,   /* match any coveritem type */
                                callback, NULL);
    if (matches==0)
        printf("No matches for path\n");
    else 
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
}

int
main(int argc, char* argv[])
{
    if (argc<3) {
        printf("Usage:   %s <ucdb file name> <path to object>\n",argv[0]);
        printf("Purpose: Remove the named objects in a UCDB.\n");
        return 1;
    }
    ucdb_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1],argv[2]);
    return 0;
}
