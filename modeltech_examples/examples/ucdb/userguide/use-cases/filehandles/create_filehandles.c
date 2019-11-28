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
 *  Usage: create_filehandles
 *
 *  This adds some file handles to the UCDB file generated in this directory.
 *  
 *****************************************************************************/
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>

const char* UCDBFILE = "test.ucdb";

/*
 *  Create a statement bin under the given parent, at the given line number,
 *  with the given count.  Create from a file number to reference an
 *  offset of an existing file table (created by Questa in this case under
 *  the design unit.)
 */
void
create_statement_with_filenumber(ucdbT db,
                 ucdbScopeT parent,
                 ucdbScopeT filetable_scope,
                 int filenumber,
                 int line,
                 int count)
{
    ucdbCoverDataT coverdata;
    ucdbSourceInfoT srcinfo;
    ucdbFileHandleT filehandle;
    ucdbAttrValueT attrvalue;
    int coverindex;
    ucdb_CreateFileHandleByNum(db,&filehandle,filetable_scope,filenumber);
    coverdata.type = UCDB_STMTBIN;
    coverdata.flags = UCDB_IS_32BIT;    /* data type flag */
    coverdata.data.int32 = count;       /* must be set for 32 bit flag */
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                  /* fake token # */
    coverindex = ucdb_CreateNextCover(db,parent,
                                      NULL, /* name: statements have none */
                                      &coverdata,
                                      &srcinfo);
    /* SINDEX attribute is used internally by Questa: */
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 1;
    ucdb_AttrAdd(db,parent,coverindex,UCDBKEY_STATEMENT_INDEX,&attrvalue);
}

/*
 *  Create a statement bin under the given parent, at the given line number,
 *  with the given count.
 */
void
create_statement_with_filehandle(ucdbT db,
                 ucdbScopeT parent,
                 ucdbFileHandleT filehandle,
                 int line,
                 int count)
{
    ucdbCoverDataT coverdata;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    int coverindex;
    coverdata.type = UCDB_STMTBIN;
    coverdata.flags = UCDB_IS_32BIT;    /* data type flag */
    coverdata.data.int32 = count;       /* must be set for 32 bit flag */
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                  /* fake token # */
    coverindex = ucdb_CreateNextCover(db,parent,
                                      NULL, /* name: statements have none */
                                      &coverdata,
                                      &srcinfo);
    /* SINDEX attribute is used internally by Questa: */
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 1;
    ucdb_AttrAdd(db,parent,coverindex,UCDBKEY_STATEMENT_INDEX,&attrvalue);
}

/*
 *  top-level example code
 */
void
example_code(const char* ucdbfile)
{
    ucdbT db = ucdb_Open(ucdbfile);
    const char* pwd = getenv("PWD");        /* works in UNIX shells */
    ucdbScopeT instance = ucdb_MatchScopeByPath(db,"/top");
    ucdbScopeT du = ucdb_MatchDU(db,"work.top");
    ucdbFileHandleT filehandle;

    printf("Adding file handles and statements to UCDB file '%s'\n", ucdbfile);

    /* Let UCDB API create a global file table for each unique filename: */
    ucdb_CreateSrcFileHandleByName(db,&filehandle,
                                   NULL,    /* let API create file table */
                                   "test.sv",
                                   pwd);
    create_statement_with_filehandle(db,instance,filehandle,3,1);

    /* Re-use file table from DU: */
    create_statement_with_filenumber(db,instance,du,0,4,1);
    create_statement_with_filenumber(db,instance,du,1,1,1);

    /* To workaround a bug: */
    ucdb_SetScopeFlag(db,du,UCDB_INST_ONCE,1);
    ucdb_SetScopeFlag(db,instance,UCDB_INST_ONCE,1);

    ucdb_Write(db,ucdbfile,NULL,1,-1);
}


/*
 *  Error handler and main program
 */
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
    ucdb_RegisterErrorHandler(error_handler, NULL);
    example_code(UCDBFILE);
    return 0;
}
