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
 *  Usage: create_ucdb
 *
 *  This creates a UCDB from scratch that is almost the same as one created by
 *  Questa.  THIS IS A WRITE STREAMING EXAMPLE ADAPTED FROM THE SIBLING
 *  "create-ucdb" EXAMPLE.
 *  
 *  Differences are:
 *  -   The test data record does not have the same contents, specifically:
 *      date and userid.  The RUNCWD attribute is not created.
 *  -   The "DUSIGNATURE" attribute is faked in this example.  This is used to
 *      detect source code changes by Questa.
 *  -   Token numbers are not reproduced as Questa produces them.
 *  -   This does not create "pragma-excluded" statements that are internal to
 *      the covergroup implementation (lines 13, 14, and 15).  Eventually
 *      Questa will not produce them, either.
 *  -   This hardcodes the 32-bit data flag.
 *  -   This does not produce the sample-count enhancement flags (value
 *      0x00200000, UCDB_BIN_SAMPLE_TRUE) produced by Questa.
 *  -   This does not produce the memory statistic attributes produced by
 *      Questa.
 *
 *  Note: the UCDB covergroup data model changed somewhat with Questa 6.4 to
 *  accommodate SV 2009 covergroup options.  Select the release with the
 *  QUESTA_RELEASE preprocessor #define.
 *  
 *****************************************************************************/
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>

#define QUESTA_RELEASE 64   /* valid values: 63 64 */

const char* UCDBFILE = "test_API.ucdb";

/*
 *  Create a design unit of the given name.
 *  Note: this hardcodes INST_ONCE and all code coverage enabled (without
 *  extended toggle coverage).
 */
void
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
                               UCDB_ENABLED_STMT | UCDB_ENABLED_BRANCH |
                               UCDB_ENABLED_COND | UCDB_ENABLED_EXPR |
                               UCDB_ENABLED_FSM | UCDB_ENABLED_TOGGLE |
                               UCDB_INST_ONCE | UCDB_SCOPE_UNDER_DU);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "FAKE DU SIGNATURE";
    ucdb_AttrAdd(db,duscope,-1,UCDBKEY_DUSIGNATURE,&attrvalue);
    ucdb_WriteStreamScope(db);      /* terminate scope object write */
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
 *  Create test data.  For the most part, this is hardcoded to be identical to
 *  the test data for the example created with Questa.
 */
void
create_testdata(ucdbT db,
                const char* ucdbfile)
{
    ucdb_AddTest(db,
        ucdbfile,
        "test",                 /* test name */
        UCDB_TESTSTATUS_OK,     /* test status */
        0.0,                    /* simulation time */
        "ns",                   /* simulation time units */
        0.0,                    /* CPU time */
        "0",                    /* random seed */
        NULL,                   /* test script: not used by Questa */
                                /* simulator arguments: */
        "-coverage -do 'run -all; coverage save test.ucdb; quit' -c top ",
        NULL,                   /* comment */
        0,                      /* compulsory */
        "20070824143300",       /* fake date */
        "userid"                /* fake userid */
        );
    ucdb_WriteStream(db);       /* terminate test data write */
}

/*
 *  Create instance of the given design design unit.
 *  This assumes INST_ONCE
 */
void
create_instance(ucdbT db,
                const char* instname,
                const char* duname)
{
    ucdb_CreateInstanceByName(db,NULL,  /* parent must be NULL! */
                        instname,
                        NULL,           /* source info: not used in Questa */
                        1,              /* weight */
                        UCDB_VLOG,      /* source language */
                        UCDB_INSTANCE,  /* instance of module/architecture */
                        (char*)duname,  /* name of design unit */
                        UCDB_INST_ONCE);/* flags */
    ucdb_WriteStream(db);       /* terminate start scope write */
}   

/*
 *  Create a statement bin under the given parent, at the given line number,
 *  with the given count.
 */
void
create_statement(ucdbT db,
                 ucdbFileHandleT filehandle,
                 int line,
                 int count)
{
    ucdbCoverDataT coverdata;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    int coverindex;
    coverdata.type = UCDB_STMTBIN;
    coverdata.flags = UCDB_IS_32BIT;    /* data type flag */
    coverdata.data.int32 = count;       /* must be set for 32 bit flag */
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                  /* fake token # */
    coverindex = ucdb_CreateNextCover(db,NULL,  /* parent must be NULL */
                                      NULL,     /* name: statements have none */
                                      &coverdata,
                                      &srcinfo);
    /* SINDEX attribute is used internally by Questa: */
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 1;
    ucdb_AttrAdd(db,NULL,coverindex,UCDBKEY_STATEMENT_INDEX,&attrvalue);
    ucdb_WriteStream(db);           /* terminate coveritem write */
}

/*
 *  Create enum toggle
 *  This hardcodes pretty much everything.
 */
void
create_enum_toggle(ucdbT db)
{
    ucdbCoverDataT coverdata;
    ucdb_CreateToggle(db,NULL,          /* parent must be NULL */
                "t",                    /* toggle name */
                NULL,                   /* canonical name */
                0,                      /* exclusions flags */
                UCDB_TOGGLE_ENUM,       /* toggle type */
                UCDB_TOGGLE_INTERNAL);  /* toggle "direction" */ 
    ucdb_WriteStream(db);               /* terminate toggle start write */
    coverdata.type = UCDB_TOGGLEBIN;
    coverdata.flags = UCDB_IS_32BIT;    /* data type flag */
    coverdata.data.int32 = 0;           /* must be set for 32 bit flag */
    ucdb_CreateNextCover(db,NULL,       /* parent must be NULL */
                         "a",           /* enum name */
                         &coverdata,
                         NULL);         /* no source data */
    ucdb_WriteStream(db);               /* terminate coveritem write */
    coverdata.data.int32 = 1;           /* must be set for 32 bit flag */
    ucdb_CreateNextCover(db,NULL,       /* parent must be NULL */
                         "b",           /* enum name */
                         &coverdata,
                         NULL);         /* no source data */
    ucdb_WriteStream(db);               /* terminate coveritem write */
    ucdb_WriteStreamScope(db);          /* terminate toggle scope write */
}

/*
 *  Create a covergroup of the given name under the given parent.
 *  This hardcodes the type_options to the defaults.
 */
void
create_covergroup(ucdbT db,
                  const char* name,
                  ucdbFileHandleT filehandle,
                  int line)
{
    ucdbScopeT cvg;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                  /* fake token # */
    cvg = ucdb_CreateScope(db,NULL,name,/* parent must be NULL */
                           &srcinfo,
                           1,           /* from type_option.weight */
                           UCDB_SV,     /* source language type */
                           UCDB_COVERGROUP,
                           0);          /* flags */
    /* Hardcoding attribute values to defaults for type_options: */
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 100;
    ucdb_AttrAdd(db,cvg,-1,UCDBKEY_GOAL,&attrvalue);
    attrvalue.u.ivalue = 0;
    ucdb_AttrAdd(db,cvg,-1,UCDBKEY_STROBE,&attrvalue);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "";
    ucdb_AttrAdd(db,cvg,-1,UCDBKEY_COMMENT,&attrvalue);
    ucdb_WriteStream(db);               /* terminate start scope write */
}

#if (QUESTA_RELEASE == 64)
void
create_coverinstance(ucdbT db,
                     const char* name,
                     ucdbFileHandleT filehandle,
                     int line)
{
    ucdbScopeT cvi;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                  /* fake token # */
    cvi = ucdb_CreateScope(db,NULL,name,/* parent must be NULL */
                           &srcinfo,
                           1,           /* from type_option.weight */
                           UCDB_SV,     /* source language type */
                           UCDB_COVERINSTANCE,
                           0);          /* flags */
    /* Hardcoding attribute values to defaults for instance options: */
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 100;
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_GOAL,&attrvalue);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "";
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_COMMENT,&attrvalue);
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 1;
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_ATLEAST,&attrvalue);
    attrvalue.u.ivalue = 64;
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_AUTOBINMAX,&attrvalue);
    attrvalue.u.ivalue = 0;
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_DETECTOVERLAP,&attrvalue);
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_PERINSTANCE,&attrvalue);
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_NUMPRINTMISSING,&attrvalue);
    attrvalue.u.ivalue = 1;
    ucdb_AttrAdd(db,cvi,-1,UCDBKEY_GETINSTCOV,&attrvalue);
    ucdb_WriteStream(db);
}
#endif

/*
 *  Create a covergroup of the given name under the given parent.
 *  This hardcodes the type_options to the defaults.
 */
void
create_coverpoint(ucdbT db,
                  const char* name,
                  ucdbFileHandleT filehandle,
                  int line,
                  int is_under_instance)
{
    ucdbScopeT cvp;
    ucdbSourceInfoT srcinfo;
    ucdbAttrValueT attrvalue;
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                  /* fake token # */
    cvp = ucdb_CreateScope(db,NULL,name,/* parent must be NULL */
                           &srcinfo,
                           1,           /* from type_option.weight */
                           UCDB_SV,     /* source language type */
                           UCDB_COVERPOINT,
                           0);          /* flags */
    /* Hardcoding attribute values to defaults for type_options: */
    attrvalue.type = UCDB_ATTR_INT;
    attrvalue.u.ivalue = 100;
    ucdb_AttrAdd(db,cvp,-1,UCDBKEY_GOAL,&attrvalue);
    attrvalue.u.ivalue = 1;
    ucdb_AttrAdd(db,cvp,-1,UCDBKEY_ATLEAST,&attrvalue);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = "";
    ucdb_AttrAdd(db,cvp,-1,UCDBKEY_COMMENT,&attrvalue);
#if (QUESTA_RELEASE == 64)
    if (is_under_instance) {
        attrvalue.type = UCDB_ATTR_INT;
        attrvalue.u.ivalue = 64;
        ucdb_AttrAdd(db,cvp,-1,UCDBKEY_AUTOBINMAX,&attrvalue);
        attrvalue.u.ivalue = 0;
        ucdb_AttrAdd(db,cvp,-1,UCDBKEY_DETECTOVERLAP,&attrvalue);
    }
#endif
    ucdb_WriteStream(db);           /* terminate start scope write */
}

/*
 *  Create a coverpoint bin of the given name, etc., under the given
 *  coverpoint.
 *  Note: the right-hand-side value for a bin is the value(s) that can cause
 *  the bin to increment if sampled.
 */
void
create_coverpoint_bin(ucdbT db,
                      const char* name,
                      ucdbFileHandleT filehandle,
                      int line,
                      int at_least,
                      int count,
                      const char* binrhs)   /* right-hand-side value */
{
    ucdbSourceInfoT srcinfo;
    ucdbCoverDataT coverdata;
    ucdbAttrValueT attrvalue;
    int coverindex;
    coverdata.type = UCDB_CVGBIN;
    coverdata.flags = UCDB_IS_32BIT | UCDB_HAS_GOAL | UCDB_HAS_WEIGHT;
    coverdata.goal = at_least;
    coverdata.weight = 1;
    coverdata.data.int32 = count;
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;                  /* fake token # */
    coverindex = ucdb_CreateNextCover(db,NULL,name,
                                      &coverdata,&srcinfo);
    attrvalue.type = UCDB_ATTR_STRING;
    attrvalue.u.svalue = binrhs;
    ucdb_AttrAdd(db,NULL,coverindex,UCDBKEY_BINRHSVALUE,&attrvalue);
    ucdb_WriteStream(db);           /* terminate start scope write */
}

/*
 *  top-level example code
 */
void
example_code(const char* ucdbfile)
{
    ucdbFileHandleT filehandle;
    ucdbT db = ucdb_OpenWriteStream(ucdbfile);
    create_testdata(db,ucdbfile);
    filehandle = create_filehandle(db,"test.sv");
    create_design_unit(db,"work.top",filehandle,0);
    create_instance(db,"top","work.top");
    create_statement(db,filehandle,6,1);
    create_statement(db,filehandle,8,1);
    create_statement(db,filehandle,9,1);
    create_enum_toggle(db);
    create_covergroup(db,"cg",filehandle,3);
    create_coverpoint(db,"t",filehandle,4,0);
    create_coverpoint_bin(db,"auto[a]",filehandle,4,1,0,"a");
    create_coverpoint_bin(db,"auto[b]",filehandle,4,1,1,"b");
    ucdb_WriteStreamScope(db);      /* terminate coverpoint */
#if (QUESTA_RELEASE == 64)
    /*
     *  6.4 stores covergroup instances:
     */
    create_coverinstance(db,"\\/top/cv ",filehandle,16);
    create_coverpoint(db,"t",filehandle,14,1);
    create_coverpoint_bin(db,"auto[a]",filehandle,14,1,0,"a");
    create_coverpoint_bin(db,"auto[b]",filehandle,14,1,1,"b");
    ucdb_WriteStreamScope(db);      /* terminate coverpoint */
    ucdb_WriteStreamScope(db);      /* terminate coverinstance */
#endif
    ucdb_WriteStreamScope(db);      /* terminate covergroup */
    ucdb_WriteStreamScope(db);      /* terminate instance */
    printf("Writing UCDB file '%s'\n", ucdbfile);
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
    ucdb_RegisterErrorHandler(error_handler, NULL);
    example_code(UCDBFILE);
    return 0;
}
