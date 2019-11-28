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
 *  Read coveritem counts in a UCDB.
 *
 *****************************************************************************/
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>

/*
 *  This function prints the coverage count or coverage vector to stdout.
 */
void
print_coverage_count(ucdbCoverDataT* coverdata)
{
    if (coverdata->flags & UCDB_IS_32BIT) {
        /* 32-bit count: */
        printf("%d", coverdata->data.int32);
    } else if (coverdata->flags & UCDB_IS_64BIT) {
        /* 64-bit count: */
#if defined (_WIN64)
        printf("%I64d", (long long)coverdata->data.int64);
#else
        printf("%lld", (long long)coverdata->data.int64);
#endif
    } else if (coverdata->flags & UCDB_IS_VECTOR) {
        /* bit vector coveritem: */
        int bytelen = coverdata->bitlen/8 + (coverdata->bitlen%8)?1:0;
        int i;
        for ( i=0; i<bytelen; i++ ) {
            if (i) printf(" ");
            printf("%02x",coverdata->data.bytevector[i]);
        }
    }
}

/* Callback to report coveritem count */
ucdbCBReturnT
callback(
    void*           userdata,
    ucdbCBDataT*    cbdata)
{
    ucdbScopeT scope = (ucdbScopeT)(cbdata->obj);
    ucdbT db = cbdata->db;
    char* name;
    ucdbCoverDataT coverdata;
    ucdbSourceInfoT sourceinfo;

    switch (cbdata->reason) {
    case UCDB_REASON_DU:
        /* Don't traverse data under a DU: see read-coverage2 */
        return UCDB_SCAN_PRUNE;
    case UCDB_REASON_CVBIN:
        scope = (ucdbScopeT)(cbdata->obj);
        /* Get coveritem data from scope and coverindex passed in: */
        ucdb_GetCoverData(db,scope,cbdata->coverindex,
                          &name,&coverdata,&sourceinfo);
        if (name!=NULL && name[0]!='\0') {
            /* Coveritem has a name, use it: */
            printf("%s%c%s: ",ucdb_GetScopeHierName(db,scope),
                   ucdb_GetPathSeparator(db),name);
        } else {
            /* Coveritem has no name, use [file:line] instead: */
            printf("%s [%s:%d]: ",ucdb_GetScopeHierName(db,scope),
                   ucdb_GetFileName(db,&sourceinfo.filehandle),
                   sourceinfo.line);
        }
        print_coverage_count(&coverdata);
        printf("\n");
        break;
    default: break;
    }
    return UCDB_SCAN_CONTINUE;
}

void
example_code(const char* ucdbfile)
{
    ucdbT db = ucdb_Open(ucdbfile);
    if (db==NULL)
        return;
    ucdb_CallBack(db,NULL,callback,NULL);
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
    if (argc<2) {
        printf("Usage:   %s <ucdb file name>\n",argv[0]);
        printf("Purpose: Read coveritem counts in a UCDB.\n");
        return 1;
    }
    ucdb_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1]);
    return 0;
}
