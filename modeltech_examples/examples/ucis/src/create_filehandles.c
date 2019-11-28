/******************************************************************************
 * UCIS API Example
 *
 * Usage: create_filehandles
 *
 * This adds some file handles to the UCDB file generated in this directory.
 *
 *****************************************************************************/
#include "ucis.h"
#include <stdio.h>
#include <stdlib.h>
const char* UCDBFILE = "test_API.ucis";
/*
 * Create a statement bin under the given parent, at the given line number,
 * with the given count.
 */
void
create_statement_with_filehandle(ucisT db,
                                 ucisScopeT parent,
                                 ucisFileHandleT filehandle,
                                 int line,
                                 int count)
{
    ucisCoverDataT coverdata;
    ucisSourceInfoT srcinfo;
    int coverindex;
    coverdata.type = UCIS_STMTBIN;
    coverdata.flags = UCIS_IS_32BIT; /* data type flag */
    coverdata.data.int32 = count; /* must be set for 32 bit flag */
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;/* fake token # */
    coverindex = ucis_CreateNextCover(db,parent,
                                      NULL, /* name: statements have none */
                                      &coverdata,
                                      &srcinfo);
    ucis_SetIntProperty(db,parent,coverindex,UCIS_INT_STMT_INDEX,1);
}
/*
 * top-level example code
 */
void
example_code(const char* ucisfile)
{
    ucisT db = ucis_Open(ucisfile);
    const char* pwd = getenv("PWD"); /* works in UNIX shells */
    /*
     * Find the top level INSTANCE scope called top
     */
    ucisScopeT instance = ucis_MatchScopeByUniqueID(db,NULL,"/4:top");
    ucisFileHandleT filehandle;
    printf("Adding file handles and statements to UCDB file '%s'\n", ucisfile);
    filehandle = ucis_CreateFileHandle(db,
                                       "test.sv",
                                       pwd);
    create_statement_with_filehandle(db,instance,filehandle,3,1);
    ucis_Write(db,ucisfile,NULL,1,-1);
}
/*
 * Error handler and main program
 */
void
error_handler(void *data,
              ucisErrorT *errorInfo)
{
    fprintf(stderr, "UCDB Error %d: %s\n",
            errorInfo->msgno, errorInfo->msgstr);
    if (errorInfo->severity == UCIS_MSG_ERROR)
        exit(1);
}
int
main(int argc, char* argv[])
{
    ucis_RegisterErrorHandler(error_handler, NULL);
    example_code(UCDBFILE);
    return 0;
}
