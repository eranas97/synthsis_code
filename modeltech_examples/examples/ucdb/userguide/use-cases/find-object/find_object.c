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
 *  Find the given scope or coveritem in a UCDB.
 *
 *****************************************************************************/
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>

void
print_scope(ucdbT db, ucdbScopeT scope)
{
    ucdbSourceInfoT sourceinfo;
    ucdb_GetScopeSourceInfo(db,scope,&sourceinfo);
#if defined(WIN32) || defined (_WIN64)
    printf("Found scope '%s': type=%016I64x line=%d\n",
           ucdb_GetScopeHierName(db,scope),
           ucdb_GetScopeType(db,scope),
           sourceinfo.line);
#else
    printf("Found scope '%s': type=%016llx line=%d\n",
           ucdb_GetScopeHierName(db,scope),
           (long long)ucdb_GetScopeType(db,scope),
           sourceinfo.line);
#endif
}

void
print_coveritem(ucdbT db, ucdbScopeT scope, int coverindex)
{
    ucdbSourceInfoT sourceinfo;
    ucdbCoverDataT coverdata;
    char* covername;
    ucdb_GetCoverData(db,scope,coverindex,&covername,&coverdata,&sourceinfo);
#if defined(WIN32) || defined(_WIN64) 
    printf("Found cover '%s/%s': types=%016I64x/%016I64x line=%d\n",
           ucdb_GetScopeHierName(db,scope),
           covername,
           ucdb_GetScopeType(db,scope),
           coverdata.type,
           sourceinfo.line);
#else
    printf("Found cover '%s/%s': types=%016llx/%016llx line=%d\n",
           ucdb_GetScopeHierName(db,scope),
           covername,
           (long long)ucdb_GetScopeType(db,scope),
           (long long)coverdata.type,
           sourceinfo.line);
#endif
}

ucdbCBReturnT
callback(
    void*           userdata,
    ucdbCBDataT*    cbdata)
{
    switch (cbdata->reason) {
    case UCDB_REASON_SCOPE:
        print_scope(cbdata->db,(ucdbScopeT)(cbdata->obj));
        break;
    case UCDB_REASON_CVBIN:
        print_coveritem(cbdata->db,(ucdbScopeT)(cbdata->obj),
                        cbdata->coverindex);
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
        printf("Usage:   %s <ucdb file name> <path to scope or cover>\n",argv[0]);
        printf("Purpose: Find a scope or coveritem by path.\n");
        return 1;
    }
    ucdb_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1],argv[2]);
    return 0;
}
