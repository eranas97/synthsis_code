/******************************************************************************
* UCIS API Example
*
* Usage: dump_filetables
*
* This dumps file tables in the given UCIS file.
*
*****************************************************************************/
#include "ucis.h"
#include <stdio.h>
#include <stdlib.h>
/*
* Dump file table for scope, global table if NULL.
*/
void
dump_filetable(ucisT db, ucisScopeT scope)
{
    int file;
    for ( file=0; file<ucis_FileTableSize(db,scope); file++ ) {
        if (file==0) {
            if (scope)
                printf("File Table for '%s':\n",
                       ucis_GetScopeHierName(db,scope));
            else
                printf("Global File Table:\n");
        }
        printf("\t%s\n", ucis_FileTableName(db,scope,file));
    }
}
/*
 * Callback for scopes and DUs.
 */
ucisCBReturnT
callback(
         void* userdata,
         ucisCBDataT* cbdata)
{
    switch (cbdata->reason) {
    case UCIS_REASON_DU:
    case UCIS_REASON_SCOPE:
        dump_filetable(cbdata->db,(ucisScopeT)(cbdata->obj));
        break;
    default: break;
    }
    return UCIS_SCAN_CONTINUE;
}
/*
 * top-level example code
 */
void
example_code(const char* ucisdb)
{
    ucisT db = ucis_Open(ucisdb);
    printf("Dumping file tables for '%s' ...\n", ucisdb);
    dump_filetable(db,NULL);
    ucis_CallBack(db,NULL,callback,NULL);
    ucis_Close(db);
}
/*
 * Error handler and main program
 */
void
error_handler(void *data,
              ucisErrorT *errorInfo)
{
    fprintf(stderr, "UCIS Error %d: %s\n",
            errorInfo->msgno, errorInfo->msgstr);
    if (errorInfo->severity == UCIS_MSG_ERROR)
        exit(1);
}
int
main(int argc, char* argv[])
{
    if (argc<2) {
        printf("Usage: %s <ucis file name>\n",argv[0]);
        printf("Purpose: Dump file tables in a UCISDB.\n");
        return 1;
    }
    ucis_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1]);
    return 0;
}
