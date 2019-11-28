/*
//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// UCDB write streaming example
//
// This example hardcodes creation of a UCDB using the "write streaming" mode.
// Write streaming is a mode of writing a UCDB that minimizes memory overhead;
// an in-memory image of the database is never created and instead small pieces
// of the database are written one at a time.  This requires a prescribed order
// of creation, which is illustrated in this file.
//
// Write streaming mode is most useful when there is already some other data
// structure in memory representing the design hierarchy and its coverage, and
// one simply wishes to traverse it and create a persistent UCDB file from it.
// 
// Note that write streaming mode maintains knowledge of the currently created
// object, and it is this object that is written each time ucdb_WriteStream and
// ucdb_WriteStreamScope are called.  The object handles are valid for writing
// attributes after creation of the object, but may not be used otherwise.
// 
// This particular example creates a design with this hierarchy:
//
//  Instance        design unit
//  top             top
//  - inst1         submodule
//    - stmt
//    - cvg
//      - cvp
//        - bin
//  - inst2         submodule
//    - stmt
//    - cvg
//      - cvp
//        - bin
//
// The "submodule" design unit type has a very simple covergroup stored in it,
// with one bin.  One of the covergroups is covered, and the other is not.
// There is in addition one code coverage statement coveritem, to illustrate
// how to create multiple objects in a single scope.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
/* UCDB API header */
#include "ucdb.h"

/*
 *  Generic error handler.
 */
void error_handler(void       *data,
                   ucdbErrorT *errorInfo)
{
    data = data;    /* ignored */
    fprintf(stderr, "UCDB error: %s\n", errorInfo->msgstr);
    if (errorInfo->severity == UCDB_MSG_ERROR)
        exit(1);
}


/*-----------------------------------------------------------------------------
 *  Write test data.
 *  This writes information about the test to the database.
 *---------------------------------------------------------------------------*/
void
write_test_data(ucdbT db)
{
    ucdbTestT testdata;
    ucdbAttrValueT attrvalue;

    /* For current time string: */
    char time_buffer[20];
    time_t current_time;

    /*
     *  Write test information.
     *  Again, ucdb_WriteStream is always required.
     *  Current time is set up as recommended for the API: note the given
     *  strftime format yields a string-sortable date constructed of integers.
     */
    (void)time(&current_time);
    (void)strftime(time_buffer,sizeof(time_buffer),"%Y%m%d%H%M%S",
        localtime(&current_time));

    testdata = ucdb_AddTest(db,
                            ucdb_Filename(db),
                            "MYTEST",
                            UCDB_TESTSTATUS_OK,
                            1.0,            /* simulation time */
                            "us",           /* simulation time units */
                            0.1,            /* CPU time */
                            "",             /* empty get_randstate string */
                            "TEST ARGS",    /* test arguments */
                            "SIM ARGS",     /* simulator arguments */
                            "MY COMMENT",   /* comment for test */
                            1,              /* compulsory test */
                            time_buffer,    /* string for current time */
                            "user");        /* id of user */

    /*
     *  Before storing the test data, let's add another user-defined attribute
     *  to it.  This must be done before the call to ucdb_WriteStream.
     */
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "MY ATTRIBUTE VALUE2";
    ucdb_AttrAdd(db,
                 testdata,      /* add attribute to test data */
                 -1,            /* only valid for coveritem attributes */
                 "MYKEY2",      /* attribute key */
                 &attrvalue);   /* attribute value */
    ucdb_WriteStream(db);
}


/*-----------------------------------------------------------------------------
 *  Write design unit to database.
 *  This writes a design unit (module declaration) to the database.
 *---------------------------------------------------------------------------*/
void
write_du(ucdbT db,
         const char* name,
         int linenum)
{
    ucdbSourceInfoT srcinfo;
    ucdbScopeT scope;
    ucdbAttrValueT attrvalue;
    const char* srcfilename = "dummyname";

    /*
     *  First set up the source info for the objects we are going to add.
     *  This sets up the "file handle" part of the source information
     *  to the given source file name:
     */
    (void)
    ucdb_CreateFileHandleByName(db,
                                &srcinfo.filehandle,    /* sets this storage */
                                NULL,                   /* NULL is simplest */
                                srcfilename);
    /*
     *  And finally this sets up the line number and token:
     */
    srcinfo.line = linenum;
    srcinfo.token = 1;

    /*
     *  Create design unit "submodule", since that is the only one that has 
     *  2 instances and requires separate storage for the design unit.
     *  
     *  Note that "parent" is never used in write streaming because the write
     *  streaming mode maintains a current context; newly created objects are
     *  added to this context.
     */
    scope = ucdb_CreateScope(db,
                             NULL,          /* no parent in streaming write */
                             name,          /* name of design unit */
                             &srcinfo,      /* file number */
                             -1,            /* no valid weight */
                             UCDB_VLOG,     /* source type */
                             UCDB_DU_MODULE,/* type of design unit */
                             UCDB_ENABLED_STMT);    /* flags */
    /*
     *  And again a user-defined attribute, just to illustrate.
     */
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 200;
    ucdb_AttrAdd(db,
                 scope,         /* add attribute to scope */
                 -1,            /* only valid for coveritem attributes */
                 "MYKEY3",      /* attribute key */
                 &attrvalue);   /* attribute value */

    /*
     *  Because we want to finish writing the design unit scope and return to
     *  the top-level of the database, this time we finish writing the database
     *  object (the design unit) with ucdb_WriteStreamScope.
     */
    ucdb_WriteStreamScope(db);
}


/*-----------------------------------------------------------------------------
 *  create_instance
 *  Create an instance of the given type.
 *---------------------------------------------------------------------------*/
void
create_instance(ucdbT db,
                const char* instname,
                const char* typename)
{
    ucdbSourceInfoT srcinfo;
    const char* srcfilename = "dummyname";

    /* See comments on source file info with create_du(), above. */
    (void)ucdb_CreateFileHandleByName(db,&srcinfo.filehandle,NULL,srcfilename);
    srcinfo.line = 1;
    srcinfo.token = 1;

    /*
     *  InstanceByName must be used with write streaming mode because the
     *  handle to the design unit type is no longer valid; we must identify it
     *  correctly by name.
     *  
     *  Note that because we are not using the ucdbScopeT returned to assign an
     *  attribute, we can skip using it at all.
     */
    (void)ucdb_CreateInstanceByName(db,
                                    NULL,          /* parent must be NULL  */
                                    instname,
                                    &srcinfo,
                                    -1,            /* no weight */
                                    UCDB_VLOG,     /* source type */
                                    UCDB_INSTANCE,
                                    (char*)typename,
                                    UCDB_ENABLED_STMT); /* flags */
}


/*-----------------------------------------------------------------------------
 *  write_instance_subhierarchy
 *  Since we have two instances that are the same, each contains the same
 *  hierarchy underneath it.
 *---------------------------------------------------------------------------*/
void
write_instance_subhierarchy(ucdbT db,
                            int covercount,
                            int stmtcount)
{
    ucdbSourceInfoT srcinfo;
    ucdbCoverDataT coverdata;
    ucdbAttrValueT attrvalue;
    const char* srcfilename = "dummyname";

    /* See comments on source file info with create_du(), above. */
    (void)ucdb_CreateFileHandleByName(db,&srcinfo.filehandle,NULL,srcfilename);
    srcinfo.line = 1;
    srcinfo.token = 1;

    /*
     *  Create a statement bin in the instance scope
     *  IMPORTANT NOTE: coveritems (like this statement bin) must be written
     *  before writing subscopes (like the following covergroup).  In other
     *  words, leaf children must be written before non-leaf children.
     */
    srcinfo.line = 83;                      /* let's make this "real" line # */
    coverdata.type = UCDB_STMTBIN;
    coverdata.flags = UCDB_IS_32BIT;
    coverdata.data.int32 = stmtcount;
    coverdata.goal = -1;
    coverdata.weight = -1;
    coverdata.limit = -1;
    (void)ucdb_CreateNextCover(db,
                           NULL,            /* parent must be NULL */
                           NULL,            /* statements have no name! */
                           &coverdata,
                           &srcinfo);

    /*
     *  Add an attribute to the coveritem (the statement bin just created
     *  above); this requires us to keep track of the index of the coveritem in
     *  the scope, 0 for 1st coveritem.
     */
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "MY ATTRIBUTE VALUE4";
    ucdb_AttrAdd(db,
                 NULL,          /* implicitly adds to current scope */
                 0,             /* add to current coveritem */
                 "MYKEY4",      /* attribute key */
                 &attrvalue);   /* attribute value */

    ucdb_WriteStream(db);                   /* write coveritem */

    /*
     *  First create a covergroup in the scope
     */
    (void)ucdb_CreateScope(db,
                           NULL,             /* parent must be null */
                           "cvg",            /* name of covergroup type */
                           &srcinfo,
                           1,                /* legitimate weight */
                           UCDB_VLOG,        /* Verilog source */
                           UCDB_COVERGROUP,  /* type */
                           UCDB_HAS_WEIGHT); /* set weight flag for scope */
    /*
     *  Important note: to represent the covergroup type options, attributes
     *  with keys like the predefined key UCDBKEY_COMMENT can be used.  These
     *  are not illustrated in this example.
     */
    ucdb_WriteStream(db);                    /* write covergroup scope */

    /*
     *  Create a coverpoint in the coverpoint scope.
     */
    (void)ucdb_CreateScope(db,
                           NULL,             /* parent must be null */
                           "cvp",            /* name of coverpoint type */
                           &srcinfo,
                           1,                /* legitimate weight */
                           UCDB_VLOG,        /* Verilog source */
                           UCDB_COVERPOINT,  /* type */
                           UCDB_HAS_WEIGHT); /* set weight flag for scope */
    ucdb_WriteStream(db);                    /* write coverpoint scope */

    /*
     *  Create a bin in the coverpoint scope.
     */
    srcinfo.line = 1;
    srcinfo.token = 1;
    coverdata.type = UCDB_CVGBIN;
    coverdata.flags = UCDB_IS_32BIT | UCDB_HAS_GOAL;
    coverdata.data.int32 = covercount;
    coverdata.goal = 1;                     /* "at_least" value */
    coverdata.weight = -1;
    coverdata.limit = -1;
    (void)ucdb_CreateNextCover(db,
                           NULL,            /* parent must be NULL */
                           "binname",       /* name */
                           &coverdata,
                           &srcinfo);
    ucdb_WriteStream(db);                   /* write coveritem */

    ucdb_WriteStreamScope(db);              /* terminate coverpoint scope */
    ucdb_WriteStreamScope(db);              /* terminate covergroup scope */

}   


/*-----------------------------------------------------------------------------
 *  Main program
 *---------------------------------------------------------------------------*/
int
main(int argc, char** argv)
{
    ucdbT db;
    const char* outputfilename = "output.ucdb";
    ucdbAttrValueT attrvalue;
    int i; /* loop variable */

    /*
     *  Register error handler.  This handles any error and immediately exits.
     */
    ucdb_RegisterErrorHandler(error_handler, NULL);

    /*
     *  Open database for write streaming mode.  Specify file in advance, as
     *  the file is written to incrementally.
     */
    db = ucdb_OpenWriteStream(outputfilename);

    /*
     *  Write global UCDB attribute.
     *  For illustrative purposes, this is a binary attribute.  It could be,
     *  for example, a file name table compacted into a single buffer.
     *  There are other attribute writing examples in this source file.
     *  Note how the ucdb_WriteStream is required to flush the output.
     */
    attrvalue.type = UCDB_ATTR_MEMBLK;
    attrvalue.u.mvalue.size = 10;
    attrvalue.u.mvalue.data = malloc(attrvalue.u.mvalue.size);
    for ( i=0; i<attrvalue.u.mvalue.size; i++) {
        /* cast to (char*) to write 1 byte at a time */
        ((char*)(attrvalue.u.mvalue.data))[i] = i;
    }
    ucdb_AttrAdd(db,
                 NULL,          /* NULL means add global attribute to UCDB */
                 -1,            /* only valid for coveritem attributes */
                 "MYKEY",       /* attribute key */
                 &attrvalue);   /* attribute value */
    free(attrvalue.u.mvalue.data);
    ucdb_WriteStream(db);       /* writes to file */

    /*
     *  Subroutines for writing parts of the database.
     */
    write_test_data(db);

    write_du(db,
             "top",             /* name of design unit */
             10);               /* line number */

    write_du(db,
             "submodule",       /* name of design unit */
             110);              /* line number */


    /*
     *  Now create the design and coverage hierarchy.  Note because of write
     *  streaming mode, parents and children scopes must be created first,
     *  followed by coveritems in a scope.  When a level is completed, the
     *  ucdb_WriteStreamScope call is made to return to the parent scope.
     *  Between siblings, the previous sibling is written with
     *  ucdb_WriteStream.
     */
    create_instance(db,
                    "top",          /* instance name */
                    "top");         /* type name */
    ucdb_WriteStream(db);           /* write instance to file */

    create_instance(db,
                    "inst1",        /* instance name */
                    "submodule");   /* type name */
    ucdb_WriteStream(db);           /* write instance to file */
    write_instance_subhierarchy(db,2,0);
    ucdb_WriteStreamScope(db);      /* finishes "inst1" instance */

    create_instance(db,
                    "inst2",        /* instance name */
                    "submodule");   /* type name */
    ucdb_WriteStream(db);           /* write instance to file */
    write_instance_subhierarchy(db,1,1);
    ucdb_WriteStreamScope(db);      /* finishes "inst2" instance */

    ucdb_WriteStreamScope(db);      /* finishes "top" instance */

    /*
     *  Close database.
     */
    ucdb_Close(db);

    printf("%s: UCDB output in file '%s'\n",
            argv[0],outputfilename);
    return 0;
}
