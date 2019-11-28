/******************************************************************************
 *  UCDB API Example
 *
 *  Copyright 2008 Mentor Graphics Corporation
 *
 *  This is the "a day in the life of a coverage datum" suggested by Accellera
 *  UCIS.
 *  
 *
 *  The coverage object corresponds exactly to this:

module top;
    int a;
    int b;
    logic clk = 0;
    always #10 clk = ~clk;

    property b_follows_a;
        @(posedge clk) a==1 ##1 b==1;
    endproperty
    mycover: cover property(b_follows_a);

    initial begin
        @(negedge clk); a = 1;
        @(negedge clk); b = 1;
        @(negedge clk); $stop;
    end
endmodule


 *  This does the following:
 *  - Creates a cover directive, named (canonically, because labeled) "mycover".
 *  - Looks up and increments the cover directive
 *  - Deletes the object from the file and saves that result to a different
 *    file.
 *
 *****************************************************************************/
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>

/*
 *  Error handler
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

/*
 *  A function to create the context for the cover directive.  This mimics a
 *  top-level instance and its corresponding design unit and test data record.
 */
ucdbScopeT
create_context(ucdbT db,
               const char* filename);

/*
 *  Create a coverage scope and pass bin under the given parent.
 */
void
create_cover(ucdbT db,
             ucdbScopeT parent)
{
    ucdbCoverDataT coverdata;
    ucdbSourceInfoT srcinfo;
    ucdbScopeT cover;
    const char* covername = "mycover";

    /*
     *  Get source information from the enclosing scope and modify it.
     */
    ucdb_GetScopeSourceInfo(db,
                            parent,
                            &srcinfo);
    srcinfo.line = 10;
    srcinfo.token = 0;

    /*
     * This is the parent of the cover pass bin.  This names the cover
     * directive.
     */
    cover = ucdb_CreateScope(db, parent,
                             covername,  /* name of scope */
                             &srcinfo,   /* source file information */
                             1,          /* weight for scope */
                             UCDB_VLOG,  /* source language type */
                             UCDB_COVER, /* scope type */
                             0);         /* flags */

    /*
     * This contains the coverage data.
     * It also names the cover directive, which is arguably unnecessary, but is
     * done in this case to duplicate what the Mentor tool does.
     * Many of the attributes -- goal, limit, etc. -- are somewhat
     * tool-specific, but the API does offer these fields as optional according
     * to the flags being set.
     */
    coverdata.type = UCDB_COVERBIN;  /* pass bin type */
    coverdata.flags = UCDB_ENABLED | UCDB_HAS_LIMIT | UCDB_HAS_WEIGHT | UCDB_HAS_GOAL
        | UCDB_IS_32BIT;
    coverdata.goal = 1;
    coverdata.weight = 1;
    coverdata.data.int32 = 1;
    coverdata.limit = -1;
    ucdb_CreateNextCover(db, cover,
                         covername,
                         &coverdata,
                         &srcinfo);
}

/*
 *  Create a UCDB with "mycover" in it.  This hardcodes the context and
 *  coverage object.
 */
void
create_ucdb(const char* filename)
{
    ucdbT db = ucdb_Open(NULL);
    ucdbScopeT toplevel = create_context(db,filename);
    create_cover(db,toplevel);
    printf("Writing UCDB file %s\n",filename);
    ucdb_Write(db,filename,NULL,1,-1);
    ucdb_Close(db);
}


/*
 *  Open the named UCDB file and increment the given cover directive.
 */
void
increment_cover(const char* filename,
                const char* covername)
{
    ucdbT db = ucdb_Open(filename);
    /*
     *  This MatchScopeByPath function works well for canonically named objects
     *  because those are guaranteed to be unique.
     */
    ucdbScopeT cover = ucdb_MatchScopeByPath(db,covername);
    if (cover) {
        /*
         *  This takes advantage of the fact that we know in this case the only
         *  bin is the pass bin.  Other algorithms are of course possible
         *  depending on the data model.
         */
        ucdb_IncrementCover(db,cover,
                            0,   /* coverindex == 0 for the only (pass) bin */
                            1);  /* amount of increment */
        /*
         *  That's it!  Save it out to the same file.
         */
        printf("Re-writing %s after increment ...\n", filename);
        ucdb_Write(db,filename,NULL,1,-1);
        ucdb_Close(db);

    } else {
        printf("Whoops: didn't find expected cover!\n");
        exit(1);
    }
}

/*
 *  Delete the given cover directive and save the deleted version of the
 *  database to a new file.
 */
void
delete_and_save(const char* inputfile,
                const char* covername,
                const char* outputfile)
{
    ucdbT db = ucdb_Open(inputfile);
    /*
     *  This MatchScopeByPath function works well for canonically named objects
     *  because those are guaranteed to be unique.
     */
    ucdbScopeT cover = ucdb_MatchScopeByPath(db,covername);
    if (cover) {
        ucdb_RemoveScope(db,cover);
        /*
         *  That's it!  Save it out to a different file.
         */
        printf("Writing %s after removing cover ...\n", outputfile);
        ucdb_Write(db,outputfile,NULL,1,-1);
        ucdb_Close(db);

    } else {
        printf("Whoops: didn't find expected cover!\n");
        exit(1);
    }
}

/*
 *  main()
 */
int
main(int argc, char* argv[])
{
    const char* filename = "test.ucdb";
    const char* newfilename = "deleted.ucdb";
    ucdb_RegisterErrorHandler(error_handler, NULL);

    create_ucdb(filename);
    increment_cover(filename,"/top/mycover");
    delete_and_save(filename,"/top/mycover",newfilename);
    return 0;
}


/*------------------------------------------------------------------------------
 *  These are some of the nuts & bolts related to creating the parts of the
 *  UCDB that are not immediately relevant to the actual coverage object in
 *  question ... but provide context (design unit or module type, top-level
 *  instance, and test data or simulator record) in which the coverage object
 *  appears.
 *----------------------------------------------------------------------------*/

/*
 *  Create a design unit of the given name.
 *  Note: this hardcodes INST_ONCE and SCOPE_UNDER_DU which arguably are not
 *  necessary.
 */
ucdbScopeT
create_design_unit(ucdbT db,
                   const char* duname,
                   ucdbFileHandleT file,
                   int line)
{
    ucdbScopeT duscope;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    srcinfo.filehandle = file;
    srcinfo.line = line;
    srcinfo.token = 0;                          /* fake token # */
    duscope = ucdb_CreateScope(db,
                               NULL,            /* DUs never have a parent */
                               duname,
                               &srcinfo,
                               1,               /* weight */
                               UCDB_VLOG,       /* source language */
                               UCDB_DU_MODULE,  /* scope type */
                               /* flags: */
                               UCDB_INST_ONCE | UCDB_SCOPE_UNDER_DU);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "FAKE DU SIGNATURE";
    ucdb_AttrAdd(db,duscope,-1,UCDBKEY_DUSIGNATURE,&attrvalue);
    return duscope;
}

/*
 *  Create a filehandle from the given file in the current directory
 *  (Works on UNIX variants only, because of the reliance on the PWD
 *  environment variable.)
 *  Note this allows the UCDB API to create a global file table; you may create
 *  your own file tables by using ucdb_SrcFileTableAppend()
 */
ucdbFileHandleT
create_filehandle(ucdbT db,
                  const char* filename)
{
    ucdbFileHandleT filehandle;
    const char* pwd = getenv("PWD");
    ucdb_CreateSrcFileHandleByName(db,&filehandle,
                                   NULL,    /* let API create file table */
                                   filename,
                                   pwd);
    return filehandle;
}

/*
 *  Create test data.  This is "inspired by" a test data record from a
 *  simulator, but obviously differs in some key respects.
 */
void
create_testdata(ucdbT db,
                const char* ucdbfile)
{
    ucdb_AddTest(db,
                 ucdbfile,
                 "test",              /* test name */
                 UCDB_TESTSTATUS_OK,  /* test status */
                 0.0,                 /* simulation time */
                 "ns",                /* simulation time units */
                 0.0,                 /* CPU time */
                 "0",                 /* random seed */
                 NULL,                /* test script: not used */
                 "dayinthelife",      /* simulator arguments! */
                 NULL,                /* comment */
                 0,                   /* compulsory */
                 "20081015150029",    /* fake date */
                 "userid"             /* fake userid */
                 );
}

/*
 *  Create instance of the given design design unit.
 *  This assumes INST_ONCE, again, arguably not necessary.
 */
ucdbScopeT
create_instance(ucdbT db,
                const char* instname,
                ucdbScopeT parent,
                ucdbScopeT duscope)
{
    return
    ucdb_CreateInstance(db,parent,instname,
                        NULL,           /* source info: not used in Questa */
                        1,              /* weight */
                        UCDB_VLOG,      /* source language */
                        UCDB_INSTANCE,  /* instance of module/architecture */
                        duscope,        /* reference to design unit */
                        UCDB_INST_ONCE);/* flags */
}   

/*
 *  Top-level function for creating context and returning a handle to it.
 */
ucdbScopeT
create_context(ucdbT db,
               const char* filename)
{
    ucdbFileHandleT filehandle;
    ucdbScopeT instance, du;
    create_testdata(db,filename);
    filehandle = create_filehandle(db,"test.sv");
    du = create_design_unit(db,"work.top",filehandle,0);
    instance = create_instance(db,"top",NULL,du);
    return instance;
}

