/******************************************************************************
* UCIS API Example
*
* Usage: increment_cover ucisname cover_UID
*
* Increment the given coveritem in a UCISDB.
*
*****************************************************************************/
#include "ucis.h"
#include <stdio.h>
#include <stdlib.h>
void
example_code(const char* ucisname, const char* path)
{
    ucisT db = ucis_Open(ucisname);
    ucisScopeT scope;
    int coverindex;
    ucisCoverDataT coverdata;
    char *name;
    ucisSourceInfoT srcinfo;

    if (db==NULL)
        return;
    scope = ucis_MatchCoverByUniqueID(db, NULL,path,&coverindex);
    ucis_GetCoverData(db,scope,coverindex,&name, &coverdata, &srcinfo);
    printf("Coverbin %s count is %d - will now add 15 to it\n", name, coverdata.data.int32);
    ucis_IncrementCover(db,scope,coverindex,15);
    ucis_GetCoverData(db,scope,coverindex,&name, &coverdata, &srcinfo);
    printf("New count is %d\n", coverdata.data.int32);
    ucis_Write(db,ucisname,
               NULL, /* save entire database */
               1, /* recurse: not necessary with NULL */
               -1); /* save all scope types */
    ucis_Close(db);
}
void
error_handler(void *data,
              ucisErrorT *errorInfo)
{
    fprintf(stderr, "UCIS Error: %s\n", errorInfo->msgstr);
    if (errorInfo->severity == UCIS_MSG_ERROR)
        exit(1);
}
int
main(int argc, char* argv[])
{
    if (argc<3) {
        printf("Usage: %s <ucisdb name> <cover UID>\n",argv[0]);
        printf("Purpose: Increment the given coveritem in a UCISDB.\n");
        return 1;
    }
    ucis_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1],argv[2]);
    return 0;
}
