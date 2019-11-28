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
 *  Usage: testplan ucdbfile
 *
 *  This is very much a hardcoded example.
 *
 *  It creates a test plan hierarchy like this:
 *
 *  testplan
 *  - section1: linked to coverpoint /top/cg/i
 *  - section2  linked to coverpoint /top/cg/j
 *****************************************************************************/
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>


void
create_and_link_testplan(const char* ucdbfile)
{
    ucdbT db = ucdb_Open(ucdbfile);
    ucdbScopeT testplan, section1, section2, cvpi, cvpj;
    if (db==0) return;

    /* Create test plan scopes: */
    testplan = ucdb_CreateScope(db,NULL,"testplan",NULL,1,UCDB_NONE,
                                UCDB_TESTPLAN,0);
    section1 = ucdb_CreateScope(db,testplan,"section1",NULL,1,UCDB_NONE,
                                UCDB_TESTPLAN,0);
    section2 = ucdb_CreateScope(db,testplan,"section2",NULL,1,UCDB_NONE,
                                UCDB_TESTPLAN,0);

    /* Look up coverpoint scopes: */
    cvpi = ucdb_MatchScopeByPath(db,"/top/cg/i");
    cvpj = ucdb_MatchScopeByPath(db,"/top/cg/j");

    /* Tag to link test plan scopes to coverpoint scopes */
    ucdb_AddObjTag(db,section1,"1");
    ucdb_AddObjTag(db,cvpi,"1");
    ucdb_AddObjTag(db,section2,"2");
    ucdb_AddObjTag(db,cvpj,"2");

    /* Write everything back to the same file */
    ucdb_Write(db,ucdbfile,NULL,1,-1);
    ucdb_Close(db);
}


void
error_handler(void *data,
              ucdbErrorT *errorInfo)
{
    fprintf(stderr, "UCDB Error %d: %s\n",
            errorInfo->msgno, errorInfo->msgstr);
    if (errorInfo->severity == UCDB_MSG_ERROR)
        exit(1);
}

int
main(int argc, char* argv[])
{
    if (argc<2) {
        printf("Expecting UCDB file as 1st argument\n");
        return 1;
    }
    ucdb_RegisterErrorHandler(error_handler, NULL);
    create_and_link_testplan(argv[1]);
    return 0;
}


