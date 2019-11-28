/******************************************************************************
 * UCIS API Example
 *
 * Find the given scope or coveritem in a UCIS from a hierarchical name
 *
 *****************************************************************************/
#include "ucis.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
void
print_scope(ucisT db, ucisScopeT scope)
{
    ucisSourceInfoT sourceinfo;
    ucis_GetScopeSourceInfo(db,scope,&sourceinfo);
    printf("Found scope '%s': type=%08x line=%d\n",
           ucis_GetStringProperty(db, scope, -1, UCIS_STR_SCOPE_HIER_NAME),
           (unsigned int) ucis_GetScopeType(db,scope),
           sourceinfo.line);
}
void
print_coveritem(ucisT db, ucisScopeT scope, int coverindex)
{
    ucisSourceInfoT sourceinfo;
    ucisCoverDataT coverdata;
    char* covername;
    ucis_GetCoverData(db,scope,coverindex,&covername,&coverdata,&sourceinfo);
    printf("Found cover '%s/%s': types=%08x/%08x line=%d\n",
           ucis_GetStringProperty(db, scope, -1, UCIS_STR_SCOPE_HIER_NAME),
           covername,
           (unsigned int) ucis_GetScopeType(db,scope),
           (unsigned int) coverdata.type,
           sourceinfo.line);
}
ucisCBReturnT
callback(
         void* userdata,
         ucisCBDataT* cbdata)
{
    switch (cbdata->reason) {
    case UCIS_REASON_SCOPE:
        if (strcmp((const char *) userdata, 
                   ucis_GetStringProperty(cbdata->db, cbdata->obj, -1, 
                                          UCIS_STR_SCOPE_HIER_NAME)) == 0)
            print_scope(cbdata->db,(ucisScopeT)(cbdata->obj));
        break;
    case UCIS_REASON_CVBIN:
        if (strcmp((const char *) userdata, 
                   ucis_GetStringProperty(cbdata->db, cbdata->obj, -1, 
                                          UCIS_STR_SCOPE_HIER_NAME)) == 0)
            print_coveritem(cbdata->db,(ucisScopeT)(cbdata->obj),
                            cbdata->coverindex);
        break;
    default: break;
    }
    return UCIS_SCAN_CONTINUE;
}
void
example_code(const char* ucisdb, const char* path)
{
    ucisT db = ucis_Open(ucisdb);
    if (db==NULL)
        return;
    ucis_CallBack(db,NULL,callback, (void *) path);
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
        printf("Usage: %s <ucisdb name> <path to scope or cover>\n",argv[0]);
        printf("Purpose: Find a scope or coveritem by path.\n");
        return 1;
    }
    ucis_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1],argv[2]);
    return 0;
}
