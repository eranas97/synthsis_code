/******************************************************************************
* UCIS API Example
*
* Usage: <program> ucisname UID
*
* Remove the named objects in a UCISDB.
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
    int coverindex = -1;
    int rc;
    char *name;
    
    if (db==NULL)
        return;

    scope = ucis_MatchScopeByUniqueID(db, NULL,path);
    if (scope) {
        printf("Removing scope %s\n",
               ucis_GetStringProperty(db,scope,
                                      coverindex,UCIS_STR_SCOPE_HIER_NAME));
        ucis_RemoveScope(db,scope);
    } else {
        scope = ucis_MatchCoverByUniqueID(db, NULL,path,&coverindex);
        if (scope) {
            ucis_GetCoverData(db,scope,coverindex,&name,NULL,NULL);
            printf("Removing cover %s/%s\n",
                   ucis_GetStringProperty(db,scope,-1,UCIS_STR_SCOPE_HIER_NAME),
                   name);
            rc = ucis_RemoveCover(db,scope,coverindex);
            if (rc!=0) {
                printf("Unable to remove cover %s/%s\n",
                       ucis_GetStringProperty(db,scope,-1,UCIS_STR_SCOPE_HIER_NAME),
                       name);
            }
        }
    }
    if (scope == NULL) {
        printf("Unable to find object matching \"%s\"\n",path);
    } else {
        ucis_Write(db,ucisname,
                   NULL, /* save entire database */
                   1, /* recurse: not necessary with NULL */
                   -1); /* save all scope types */
    }
    ucis_Close(db);
}

void
error_handler(void *data,
              ucisErrorT *errorInfo)
{
    fprintf(stderr, "UCIS Error: %s\n", errorInfo->msgstr);
}
int
main(int argc, char* argv[])
{
    if (argc<3) {
        printf("Usage: %s <ucis name> <UID>\n",argv[0]);
        printf("Purpose: Remove the identified objects in a UCISDB.\n");
        return 1;
    }
    ucis_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1],argv[2]);
    return 0;
}
