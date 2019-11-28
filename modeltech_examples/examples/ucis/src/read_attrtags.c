/******************************************************************************
* UCIS API Example
*
* Usage: <program> ucisname UID
*
* Read attributes and tags for the given object(s) in a UCISDB.
*
*****************************************************************************/
#include "ucis.h"
#include <stdio.h>
#include <stdlib.h>

void
print_tags(ucisT db, ucisScopeT scope, int coverindex)
{
    ucisIteratorT iter;
    const char *tag;
    char* covername;

    iter = ucis_ObjectTagsIterate(db,scope,coverindex);

    printf("Tags for %s",ucis_GetStringProperty(db,scope,
                                                   coverindex,UCIS_STR_SCOPE_HIER_NAME));
    if (coverindex>=0) {
        ucis_GetCoverData(db,scope,coverindex,&covername,NULL,NULL);
        printf("%c%s:\n",ucis_GetPathSeparator(db),covername);
    } else {
        printf(":\n");
    }
    if (iter) {
        while ((tag = ucis_ObjectTagsScan(db,iter))) {
            printf("   %s\n", tag);
        }
        ucis_FreeIterator(db, iter);
    }
}
void
print_attrs(ucisT db, ucisScopeT scope, int coverindex)
{
    const char* attrname;
    ucisAttrValueT* attrvalue;
    char* covername;
    printf("Attributes for %s",ucis_GetStringProperty(db,scope,
                                                   coverindex,UCIS_STR_SCOPE_HIER_NAME));
    if (coverindex>=0) {
        ucis_GetCoverData(db,scope,coverindex,&covername,NULL,NULL);
        printf("%c%s:\n",ucis_GetPathSeparator(db),covername);
    } else {
        printf(":\n");
    }
    attrname = NULL;
    while ((attrname = ucis_AttrNext(db,(ucisObjT)scope,coverindex,
                                     attrname,&attrvalue))) {
        printf("\t%s: ", attrname);
        switch (attrvalue->type)
            {
            case UCIS_ATTR_INT:
                printf("int = %d\n", attrvalue->u.ivalue);
                break;
            case UCIS_ATTR_FLOAT:
                printf("float = %f\n", attrvalue->u.fvalue);
                break;
            case UCIS_ATTR_DOUBLE:
                printf("double = %lf\n", attrvalue->u.dvalue);
                break;
            case UCIS_ATTR_STRING:
                printf("string = '%s'\n",
                       attrvalue->u.svalue ? attrvalue->u.svalue : "(null)");
                break;
            case UCIS_ATTR_MEMBLK:
                printf("binary, size = %d ", attrvalue->u.mvalue.size);
                if (attrvalue->u.mvalue.size > 0) {
                    int i;
                    printf("value = ");
                    for ( i=0; i<attrvalue->u.mvalue.size; i++ )
                        printf("%02x ", attrvalue->u.mvalue.data[i]);
                }
                printf("\n");
                break;
            default:
                printf("ERROR! UNKNOWN ATTRIBUTE TYPE (%d)\n", attrvalue->type);
            } /* end switch (attrvalue->type) */
    } /* end while (ucis_AttrNext(...)) */
}
void
example_code(const char* ucisname, const char* path)
{
    ucisT db = ucis_Open(ucisname);
    ucisScopeT scope;
    int coverindex = -1;
    
    if (db==NULL)
        return;

    scope = ucis_MatchScopeByUniqueID(db, NULL,path);
    if (scope) {
        print_tags(db, scope,coverindex);
        print_attrs(db,scope,coverindex);
    } else {
        scope = ucis_MatchCoverByUniqueID(db, NULL,path,&coverindex);
        print_tags(db, scope,coverindex);
        print_attrs(db,scope,coverindex);
    }
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
        printf("Usage: %s <ucis name> <path to scope or cover>\n",argv[0]);
        printf("Purpose: Read attributes and tags for the given object in a UCISDB.\n");
        return 1;
    }
    ucis_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1],argv[2]);
    return 0;
}
