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
 *  Read attributes and tags for the given object(s) in a UCDB.
 *
 *****************************************************************************/
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>

void
print_tags(ucdbT db, ucdbScopeT scope)
{
    int i, ntags = ucdb_GetObjNumTags(db,(ucdbObjT)scope);
    const char* tagname;
    printf("Tags for %s:\n",ucdb_GetScopeHierName(db,scope));
    if (ntags > 0) {
        for ( i=0; i<ntags; i++ ) {
            ucdb_GetObjIthTag(db,(ucdbObjT)scope,i,&tagname);
            printf("%s ",tagname);
        }
        printf("\n");
    }
}

void
print_attrs(ucdbT db, ucdbScopeT scope, int coverindex)
{
    const char* attrname;
    ucdbAttrValueT attrvalue;
    char* covername;
    printf("Attributes for %s",ucdb_GetScopeHierName(db,scope));
    if (coverindex>=0) {
        ucdb_GetCoverData(db,scope,coverindex,&covername,NULL,NULL);
        printf("%c%s:\n",ucdb_GetPathSeparator(db),
			   covername?covername:"(no name)");
    } else {
        printf(":\n");
    }
    attrname = NULL;
    while ((attrname = ucdb_AttrGetNext(db,(ucdbObjT)scope,coverindex,
                                     attrname,&attrvalue))) {
        printf("\t%s: ", attrname);
        switch (attrvalue.type)
        {
        case UCDB_ATTR_INT:
            printf("int = %d\n", attrvalue.u.ivalue);
            break;
        case UCDB_ATTR_FLOAT:
            printf("float = %f\n", attrvalue.u.fvalue);
            break;
        case UCDB_ATTR_DOUBLE:
            printf("double = %lf\n", attrvalue.u.dvalue);
            break;
        case UCDB_ATTR_STRING:
            printf("string = '%s'\n",
                   attrvalue.u.svalue ? attrvalue.u.svalue : "(null)");
            break;
        case UCDB_ATTR_MEMBLK:
            printf("binary, size = %d ", attrvalue.u.mvalue.size);
            if (attrvalue.u.mvalue.size > 0) {
                int i;
                printf("value = ");
                for ( i=0; i<attrvalue.u.mvalue.size; i++ )
                    printf("%02x ", attrvalue.u.mvalue.data[i]);
            }
            printf("\n");
            break;
        default:
            printf("ERROR! UNKNOWN ATTRIBUTE TYPE (%d)\n", attrvalue.type);
        } /* end switch (attrvalue.type) */
    } /* end while (ucdb_AttrGetNext(...)) */
}

ucdbCBReturnT
callback(
    void*           userdata,
    ucdbCBDataT*    cbdata)
{
    switch (cbdata->reason) {
    case UCDB_REASON_SCOPE:
        print_tags(cbdata->db,(ucdbScopeT)(cbdata->obj));
        print_attrs(cbdata->db,(ucdbScopeT)(cbdata->obj),-1);
        break;
    case UCDB_REASON_CVBIN:
        print_attrs(cbdata->db,(ucdbScopeT)(cbdata->obj),cbdata->coverindex);
        break;
    default: break;
    }
    return UCDB_SCAN_CONTINUE;
}

void
example_code(const char* ucdbfile, const char* path)
{
    ucdbT db = ucdb_Open(ucdbfile);
    if (db==NULL)
        return;
    ucdb_PathCallBack(db,
                      0,    /* don't recurse from found object */
                      path,
                      NULL, /* design unit name does not apply */
                      UCDB_NONTESTPLAN_SCOPE,   /* tree root type */
                      -1,   /* match any scope type */
                      -1,   /* match any coveritem type */
                      callback, NULL);
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
    if (argc<3) {
        printf("Usage:   %s <ucdb file name> <path to scope or cover>\n",argv[0]);
        printf("Purpose: Read attributes and tags for the given object in a UCDB.\n");
        return 1;
    }
    ucdb_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1],argv[2]);
    return 0;
}
