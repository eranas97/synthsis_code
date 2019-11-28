/******************************************************************************
* UCIS API Example
*
* Usage: <program> ucisname
*
* Traverse all scopes in a UCISDB in READ STREAMING.
*
*****************************************************************************/
#include "ucis.h"
#include <stdio.h>
#include <stdlib.h>
ucisCBReturnT
callback(
         void* userdata,
         ucisCBDataT* cbdata)
{
    ucisScopeT scope;
    switch (cbdata->reason) {
    case UCIS_REASON_DU:
    case UCIS_REASON_SCOPE:
        scope = (ucisScopeT)(cbdata->obj);
        printf("%s\n",ucis_GetStringProperty(cbdata->db,scope,-1,UCIS_STR_SCOPE_HIER_NAME));
        break;
    default: break;
    }
    return UCIS_SCAN_CONTINUE;
}
void
example_code(const char* ucisname)
{
    ucis_OpenReadStream(ucisname,callback,NULL);
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
    if (argc<2) {
        printf("Usage: %s <ucis name>\n",argv[0]);
        printf("Purpose: Traverse all scopes in a UCISDB in READ STREAMING.\n");
        return 1;
    }
    ucis_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1]);
    return 0;
}
