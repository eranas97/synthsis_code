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
 *  Traverse objects associated with a test plan in a UCDB.
 *
 *****************************************************************************/
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>

void
indent(int level)
{
    int i;
    for ( i=0; i<level; i++ )
        printf("   ");
}

void
recurse_testplan(int level, ucdbT db, ucdbScopeT scope)
{
    int t, numtags;
    const char* tagname;
    ucdbScopeT subscope;

    /* Print test plan scope name and recurse child test plan sections */
    indent(level);
    printf("%s\n",ucdb_GetScopeName(db,scope));
    subscope=NULL;
    while ((subscope=ucdb_NextSubScope(db,scope,subscope,UCDB_TESTPLAN))) {
        recurse_testplan(level+1,db,subscope);
    }

    /* from ucdb.h: traverse non-testplan objects with the same tag name */
    numtags = ucdb_GetObjNumTags(db,(ucdbObjT)scope);
    for ( t=0; t<numtags; t++ ) {
        int found;
        ucdbObjT taggedobj; 
        ucdb_GetObjIthTag(db,(ucdbObjT)scope,t,&tagname);
        for ( found=ucdb_BeginTaggedObj(db,tagname,&taggedobj);
              found; found=ucdb_NextTaggedObj(db,&taggedobj) ) {
            if (ucdb_ObjKind(db,taggedobj)==UCDB_OBJ_SCOPE
                && ucdb_GetScopeType(db,(ucdbScopeT)taggedobj)==UCDB_TESTPLAN)
                continue;
            /* tagged object is not a test plan scope: */
            indent(level+1);
            if (ucdb_ObjKind(db,taggedobj)==UCDB_OBJ_SCOPE)
                printf("%s\n",ucdb_GetScopeHierName(db,(ucdbScopeT)taggedobj));
            else if (ucdb_ObjKind(db,taggedobj)==UCDB_OBJ_TESTDATA)
                printf("%s\n",ucdb_GetTestName(db,(ucdbTestT)taggedobj));
        }
    }
}

void
example_code(const char* ucdbfile)
{
    ucdbScopeT subscope;
    ucdbT db = ucdb_Open(ucdbfile);
    if (db==NULL)
        return;
    subscope=NULL;
    while ((subscope=ucdb_NextSubScope(db,NULL,subscope,UCDB_TESTPLAN))) {
        recurse_testplan(0,db,subscope);
    }
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
        printf("Purpose: Traverse objects associated with a test plan in a UCDB.\n");
        return 1;
    }
    ucdb_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1]);
    return 0;
}
