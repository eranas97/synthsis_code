/******************************************************************************
* UCIS API Example
*
* Usage: <program> ucisname
*
* Read coveritem counts in a UCISDB.
*
*****************************************************************************/
#include "ucis.h"
#include <stdio.h>
#include <stdlib.h>
/*
* This function prints the coverage count or coverage vector to stdout.
*/
void
print_coverage_count(ucisCoverDataT* coverdata)
{
    if (coverdata->flags & UCIS_IS_32BIT) {
        /* 32-bit count: */
        printf("%d", coverdata->data.int32);
    } else if (coverdata->flags & UCIS_IS_64BIT) {
        /* 64-bit count: */
        /* printf formatting is platform-dependent */
#if defined(_MSC_VER)
        printf("%I64d", coverdata->data.int64);
#elif defined(__LP64__) || defined(_LP64)
        printf("%ld", coverdata->data.int64);
#else
        printf("%lld", coverdata->data.int64);
#endif
    } else if (coverdata->flags & UCIS_IS_VECTOR) {
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
ucisCBReturnT
callback(
         void* userdata,
         ucisCBDataT* cbdata)
{
    ucisScopeT scope = (ucisScopeT)(cbdata->obj);
    ucisT db = cbdata->db;
    char* name;
    ucisCoverDataT coverdata;
    ucisSourceInfoT sourceinfo;
    switch (cbdata->reason) {
    case UCIS_REASON_DU:
        /* Don't traverse data under a DU: see read-coverage2 */
        return UCIS_SCAN_PRUNE;
    case UCIS_REASON_CVBIN:
        scope = (ucisScopeT)(cbdata->obj);
        /* Get coveritem data from scope and coverindex passed in: */
        ucis_GetCoverData(db,scope,cbdata->coverindex,
                          &name,&coverdata,&sourceinfo);
        if (name!=NULL && name[0]!='\0') {
            /* Coveritem has a name, use it: */
            printf("%s%c%s: ",
                   ucis_GetStringProperty(db,scope,-1,UCIS_STR_SCOPE_HIER_NAME),
                   ucis_GetPathSeparator(db),name);
        } else {
            /* Coveritem has no name, use [file:line] instead: */
            printf("%s [%s:%d]: ",
                   ucis_GetStringProperty(db,scope,-1,UCIS_STR_SCOPE_HIER_NAME),
                   ucis_GetFileName(db,&sourceinfo.filehandle),
                   sourceinfo.line);
        }
        print_coverage_count(&coverdata);
        printf("\n");
        break;
    default: break;
    }
    return UCIS_SCAN_CONTINUE;
}
void
example_code(const char* ucisname)
{
    ucisT db = ucis_Open(ucisname);
    if (db==NULL)
        return;
    ucis_CallBack(db,NULL,callback,NULL);
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
    if (argc<2) {
        printf("Usage: %s <ucis name>\n",argv[0]);
        printf("Purpose: Read coveritem counts in a UCISDB.\n");
        return 1;
    }
    ucis_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1]);
    return 0;
}
