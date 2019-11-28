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
 *  Usage: dump_filetables
 *
 *  This dumps file tables in the given UCDB file.
 *  
 *****************************************************************************/
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>


/*
 *	Dump file table for scope, global table if NULL.
 */
void
dump_filetable(ucdbT db, ucdbScopeT scope)
{
	int file;
	for ( file=0; file<ucdb_FileTableSize(db,scope); file++ ) {
		if (file==0) {
			if (scope)
				printf("File Table for '%s':\n",
					   ucdb_GetScopeHierName(db,scope));
			else	
				printf("Global File Table:\n");
		}
		printf("\t%s\n", ucdb_FileTableName(db,scope,file));
	}
}

/*
 *	Callback for scopes and DUs.
 */
ucdbCBReturnT
callback(
    void*           userdata,
    ucdbCBDataT*    cbdata)
{
    switch (cbdata->reason) {
    case UCDB_REASON_DU:
    case UCDB_REASON_SCOPE:
		dump_filetable(cbdata->db,(ucdbScopeT)(cbdata->obj));
        break;
    default: break;
    }
    return UCDB_SCAN_CONTINUE;
}

/*
 *  top-level example code
 */
void
example_code(const char* ucdbfile)
{
    ucdbT db = ucdb_Open(ucdbfile);
	printf("Dumping file tables for '%s' ...\n", ucdbfile);
	dump_filetable(db,NULL);
	ucdb_CallBack(db,NULL,callback,NULL);
    ucdb_Close(db);
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
    if (argc<2) {
        printf("Usage:   %s <ucdb file name>\n",argv[0]);
        printf("Purpose: Dump file tables in a UCDB file.\n");
        return 1;
    }
    ucdb_RegisterErrorHandler(error_handler, NULL);
    example_code(argv[1]);
    return 0;
}
