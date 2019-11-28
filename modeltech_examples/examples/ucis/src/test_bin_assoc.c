/******************************************************************************
* UCIS API Example
*
* Usage: test_bin_assoc
*
*****************************************************************************/
#include "ucis.h"
#include <stdio.h>
#include <stdlib.h>
const char* UCISDB = "assoc_API.ucis";
/*
 * Basic UCISDB creation requires design unit and filehandle
 */
ucisScopeT
create_design_unit(ucisT db,
                   const char* duname,
                   ucisFileHandleT file,
                   int line)
{
    ucisScopeT duscope;
    ucisSourceInfoT srcinfo;
    srcinfo.filehandle = file;
    srcinfo.line = line;
    srcinfo.token = 0; /* fake token # */
    duscope = ucis_CreateScope(db,
                               NULL, /* DUs never have a parent */
                               duname,
                               &srcinfo,
                               1, /* weight */
                               UCIS_VLOG, /* source language */
                               UCIS_DU_MODULE, /* scope type */
                               /* flags: */
                               UCIS_ENABLED_STMT | UCIS_ENABLED_BRANCH |
                               UCIS_ENABLED_COND | UCIS_ENABLED_EXPR |
                               UCIS_ENABLED_FSM | UCIS_ENABLED_TOGGLE |
                               UCIS_INST_ONCE | UCIS_SCOPE_UNDER_DU);
    ucis_SetStringProperty(db,duscope,-1,UCIS_STR_DU_SIGNATURE,"FAKE DU SIGNATURE");
    return duscope;
}
ucisFileHandleT
create_filehandle(ucisT db,
                  const char* filename)
{
    ucisFileHandleT filehandle;
    const char* pwd = getenv("PWD");
    filehandle = ucis_CreateFileHandle(db,
                                       filename,
                                       pwd);
    return filehandle;
}
/*
 * Create history nodes. We will create 10 separate test records, as if
 * this UCIS file had included 10 tests, plus a merge record to record the
 * merge process
 * The 10 handles are loaded into the TRarray for the caller.
 * This example does not show setting the testdata
 * The logical names must differ as they are the primary keys,
 * in a real environment these names should have some meaning.
 */
void
create_testdata(ucisT db,
                const char* ucisdb,
                ucisHistoryNodeT *TRarray)
{
    char logical_name[10];
    int i;
    ucisHistoryNodeT mergenode;

    /* one merge record (all the test records will be children of this record) */
    mergenode = ucis_CreateHistoryNode(db,
                                       NULL,
                                       "TopHistoryNode",
                                       (char *) ucisdb,
                                       UCIS_HISTORYNODE_MERGE);
    
    /*
     * Create ten test records named Test1 through Test10
     * Handles to them are stored in TRarray[1] through TRarray[10]
     */
    for (i=1; i<=10; i++) {
        sprintf(logical_name, "Test%d", i); /* force a new logical name each time */
        TRarray[i] =  ucis_CreateHistoryNode(
                                           db,
                                           mergenode,
                                           logical_name,
                                           (char *) ucisdb,
                                           UCIS_HISTORYNODE_TEST);
    }
}
ucisScopeT
create_instance(ucisT db,
                const char* instname,
                ucisScopeT parent,
                ucisScopeT duscope)
{
    return
        ucis_CreateInstance(db,parent,instname,
                            NULL, /* source info: not used */
                            1, /* weight */
                            UCIS_VLOG, /* source language */
                            UCIS_INSTANCE, /* instance of module/architecture */
                            duscope, /* reference to design unit */
                            UCIS_INST_ONCE); /* flags */
}
/*
 * Create a statement bin under the given parent, at the given line number,
 * with the given count.
 */
void
create_statement(ucisT db,
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
example_code(const char* ucisdb)
{
    ucisFileHandleT filehandle;
    ucisScopeT instance, du;
    ucisT db = ucis_Open(NULL);
    ucisHistoryNodeT TRarray[11]; /* test records, TRarray[0] is unused */
    ucisHistoryNodeT test;
    ucisHistoryNodeListT testlist;
    ucisIteratorT bin_iterator, test_iterator;
    int i, index;

    create_testdata(db,ucisdb, TRarray); /* load test record handles into array */
    filehandle = create_filehandle(db,"test.sv");
    du = create_design_unit(db,"work.top",filehandle,0);
    instance = create_instance(db,"top",NULL,du);
    /*
     * Create 10 statement bins under the same instance
     * We can assume that these will be coverindexes 0-19
     */
    for (i=1; i<=10; i++) {
        create_statement(db,instance,filehandle,i,1);
    }

    /*
     * The UCISDB now has 10 test records and 10 statement bins.
     * The history node list association routines allow definition
     * of any many-to-many association between bins and tests
     * We will demonstrate associating 3 tests with the statement bin
     * coverindex 4, and 4 tests with bin 6
     */

    /*
     * First we must create the list of test nodes we want to associate with a bin
     * The steps are
     * 1. create the list object
     * 2. add each desired test object to the list
     */
    testlist = ucis_CreateHistoryNodeList(db);
    printf("Add tests \"%s\" \"%s\" and \"%s\" to the list\n",
           ucis_GetStringProperty(db, TRarray[3], -1, UCIS_STR_HIST_LOG_NAME),
           ucis_GetStringProperty(db, TRarray[8], -1, UCIS_STR_HIST_LOG_NAME),
           ucis_GetStringProperty(db, TRarray[9], -1, UCIS_STR_HIST_LOG_NAME)
           );
    ucis_AddToHistoryNodeList(db,testlist,TRarray[3]);
    ucis_AddToHistoryNodeList(db,testlist,TRarray[8]);
    ucis_AddToHistoryNodeList(db,testlist,TRarray[9]);

    /*
     * We have constructed a test list of three tests. 
     * Next, associate this list with the chosen statement bin, coverindex 4
     * The meaning of the association is "tests that hit the bin". This
     * is a pre-defined semantic association.
     */

    ucis_SetHistoryNodeListAssoc(db, instance, 4, testlist, UCIS_ASSOC_TESTHIT);

    /*
     * Add another test and associate it with bin coverindex 6
     */

    printf("Add test \"%s\" to the list\n",
           ucis_GetStringProperty(db, TRarray[2], -1, UCIS_STR_HIST_LOG_NAME));
    ucis_AddToHistoryNodeList(db,testlist,TRarray[2]);
    ucis_SetHistoryNodeListAssoc(db, instance, 6, testlist, UCIS_ASSOC_TESTHIT);

    /*
     * Free the testlist; the data has been applied to the database
     * and the list itself is no longer needed
     */
    ucis_FreeHistoryNodeList(db, testlist);

    /*
     * Verification phase.
     * Iterate all the bins and report the associated tests
     * (we expect to discover tests associated with the 4th and 6th bins)
     */

    bin_iterator = ucis_CoverIterate(db, instance, 0);
    for (index = ucis_CoverScan(db,bin_iterator);
         index >= 0;
         index = ucis_CoverScan(db,bin_iterator)) {
        printf("Cover item %s Index %d tests:\n",
               ucis_GetStringProperty(db, instance, -1, UCIS_STR_SCOPE_HIER_NAME),
               index);
        testlist = ucis_GetHistoryNodeListAssoc(db, instance, index, UCIS_ASSOC_TESTHIT);
        if (testlist) {
            test_iterator = ucis_HistoryNodeListIterate(db, testlist);
            while ((test = ucis_HistoryScan(db,test_iterator))) {
                /* 
                 * 'test' is now a test history node handleUCIS_STR_HIST_LOG_NAME
                 */
                printf("   %s\n",
                       ucis_GetStringProperty(db, test, -1, UCIS_STR_HIST_LOG_NAME));
            }
            ucis_FreeIterator(db, test_iterator);
        } else {
            printf("   0 tests found\n");
        }
    }
    ucis_FreeIterator(db, bin_iterator);
    printf("Writing UCISDB file '%s'\n", ucisdb);
    ucis_Write(db,ucisdb,NULL,1,-1);
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
    ucis_RegisterErrorHandler(error_handler, NULL);
    example_code(UCISDB);
    return 0;
}
