/******************************************************************************
 * UCIS API Example
 *
 * Usage: create_ucis
 *
 * This creates a UCISDB from scratch.
 * THIS IS A WRITE STREAMING EXAMPLE ADAPTED FROM THE SIBLING
 * "create-ucis" EXAMPLE.
 *
 *****************************************************************************/
#include "ucis.h"
#include <stdio.h>
#include <stdlib.h>
const char* UCISDB = "test_ws.ucis";
/*
 * Create a design unit of the given name.
 * Note: this hardcodes INST_ONCE and all code coverage enabled (without
 * extended toggle coverage).
 */
void
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
    ucis_WriteStreamScope(db); /* terminate scope object write */
}
/*
 * Create a filehandle from the given file in the current directory
 * (Works on UNIX variants only, because of the reliance on the PWD
 * environment variable.)
 */
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
 * Create test data. For the most part, this is hardcoded.
 */
void
create_testdata(ucisT db,
                const char* ucisdb)
{
    ucisHistoryNodeT testnode;
    /*
    ucisTestDataT    testdata = {
        UCIS_TESTSTATUS_OK,  // teststatus
    0.0,                     // simtime
        "ns",                // timeunit
        "./",                // runcwd
        0.0,                 // cputime
        "0",                 // seed
        "toolname",          // cmd
        "command arguments", // args
        0,                   // compulsory
        "20110824143300",    // date
        "ucis_user",         // username
        0.0,                 // cost
        "UCIS:Simulator"     // toolcategory
    };
    */
    testnode =  ucis_CreateHistoryNode(
               db,
               NULL,                /* no parent since it is the only one */
               "TestLogicalName",   /* primary key, never NULL */
               (char *) ucisdb,     /* optional physical name at creation */
               UCIS_HISTORYNODE_TEST);  /* It's a test history node */
    
    ucis_WriteStream(db); /* terminate test data write */
}
/*
 * Create instance of the given design design unit.
 * This assumes INST_ONCE
 */
void
create_instance(ucisT db,
                const char* instname,
                const char* duname)
{
    ucis_CreateInstanceByName(db,NULL, /* parent must be NULL! */
                              instname,
                              NULL, /* source info: not used */
                              1, /* weight */
                              UCIS_VLOG, /* source language */
                              UCIS_INSTANCE, /* instance of module/architecture */
                              (char*)duname, /* name of design unit */
                              UCIS_INST_ONCE); /* flags */
    ucis_WriteStream(db); /* terminate start scope write */
}
/*
 * Create a statement bin under the given parent, at the given line number,
 * with the given count.
 */
void
create_statement(ucisT db,
                 ucisFileHandleT filehandle,
                 int fileno, /* 1-referenced wrt DU contributing files */
                 int line,   /* 1-referenced wrt file */
                 int item,   /* 1-referenced wrt statements starting on the line */
                 int count)
{
    ucisCoverDataT coverdata;
    ucisSourceInfoT srcinfo;
    int coverindex;
    char name[25];
    /* UOR name generation */
    sprintf(name,"#stmt#%d#%d#%d#",fileno, line, item);

    coverdata.type = UCIS_STMTBIN;
    coverdata.flags = UCIS_IS_32BIT; /* data type flag */
    coverdata.data.int32 = count; /* must be set for 32 bit flag */
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 17;/* fake token # */
    coverindex = ucis_CreateNextCover(db,NULL, /* parent must be NULL */
                                      name,
                                      &coverdata,
                                      &srcinfo);
    ucis_SetIntProperty(db,NULL,coverindex,UCIS_INT_STMT_INDEX,item);
    ucis_WriteStream(db); /* terminate coveritem write */
}
/*
 * Create enum toggle
 * This hardcodes pretty much everything.
 */
void
create_enum_toggle(ucisT db)
{
    ucisCoverDataT coverdata;
    ucis_CreateToggle(db,NULL,
                      "t", /* toggle name */
                      NULL, /* canonical name */
                      0, /* exclusions flags */
                      UCIS_TOGGLE_METRIC_ENUM, /* metric */
                      UCIS_TOGGLE_TYPE_REG,    /* type */
                      UCIS_TOGGLE_DIR_INTERNAL); /* toggle "direction" */
    ucis_WriteStream(db); /* terminate toggle start write */
    coverdata.type = UCIS_TOGGLEBIN;
    coverdata.flags = UCIS_IS_32BIT; /* data type flag */
    coverdata.data.int32 = 0; /* must be set for 32 bit flag */
    ucis_CreateNextCover(db,NULL, /* parent must be NULL */
                         "a", /* enum name */
                         &coverdata,
                         NULL); /* no source data */
    ucis_WriteStream(db); /* terminate coveritem write */
    coverdata.data.int32 = 1; /* must be set for 32 bit flag */
    ucis_CreateNextCover(db,NULL, /* parent must be NULL */
                         "b", /* enum name */
                         &coverdata,
                         NULL); /* no source data */
    ucis_WriteStream(db); /* terminate coveritem write */
    ucis_WriteStreamScope(db); /* terminate toggle scope write */
}
/*
 * Create a covergroup of the given name under the given parent.
 * This hardcodes the type_options to the defaults.
 */
void
create_covergroup(ucisT db,
                  const char* name,
                  ucisFileHandleT filehandle,
                  int line)
{
    ucisScopeT cvg;
    ucisSourceInfoT srcinfo;

    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0; /* fake token # */
    cvg = ucis_CreateScope(db,NULL,name, /* parent must be NULL */
                           &srcinfo,
                           1, /* from type_option.weight */
                           UCIS_VLOG, /* source language type */
                           UCIS_COVERGROUP,
                           0); /* flags */
    /* Hardcoding attribute values to defaults for type_options: */
    ucis_SetIntProperty(db,cvg,-1,UCIS_INT_STMT_INDEX,1);
    ucis_SetIntProperty(db,cvg,-1,UCIS_INT_SCOPE_GOAL,100);
    ucis_SetIntProperty(db,cvg,-1,UCIS_INT_CVG_STROBE,0);
    ucis_SetStringProperty(db,cvg,-1,UCIS_STR_COMMENT,"");
    ucis_WriteStream(db); /* terminate start scope write */
}
/*
 * Create a covergroup of the given name under the given parent.
 * This hardcodes the type_options to the defaults.
 */
void
create_coverpoint(ucisT db,
                  const char* name,
                  ucisFileHandleT filehandle,
                  int line)
{
    ucisScopeT cvp;
    ucisSourceInfoT srcinfo;

    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0; /* fake token # */
    cvp = ucis_CreateScope(db,NULL,name, /* parent must be NULL */
                           &srcinfo,
                           1, /* from type_option.weight */
                           UCIS_VLOG, /* source language type */
                           UCIS_COVERPOINT,
                           0); /* flags */
    /* Hardcoding attribute values to defaults for type_options: */
    ucis_SetIntProperty(db,cvp,-1,UCIS_INT_SCOPE_GOAL,100);
    ucis_SetIntProperty(db,cvp,-1,UCIS_INT_CVG_ATLEAST,1);
    ucis_SetStringProperty(db,cvp,-1,UCIS_STR_COMMENT,"");
    ucis_WriteStream(db); /* terminate start scope write */
}
/*
 * Create a coverpoint bin of the given name, etc., under the given
 * coverpoint.
 * Note: the right-hand-side value for a bin is the value(s) that can cause
 * the bin to increment if sampled.
 */
void
create_coverpoint_bin(ucisT db,
                      const char* name,
                      ucisFileHandleT filehandle,
                      int line,
                      int at_least,
                      int count,
                      const char* binrhs) /* right-hand-side value */
{
    ucisSourceInfoT srcinfo;
    ucisCoverDataT coverdata;
    int coverindex;

    coverdata.type = UCIS_CVGBIN;
    coverdata.flags = UCIS_IS_32BIT | UCIS_HAS_GOAL | UCIS_HAS_WEIGHT;
    coverdata.goal = at_least;
    coverdata.weight = 1;
    coverdata.data.int32 = count;
    srcinfo.filehandle = filehandle;
    srcinfo.line = line;
    srcinfo.token = 0;/* fake token # */
    coverindex = ucis_CreateNextCover(db,NULL,name,
                                      &coverdata,&srcinfo);
    ucis_WriteStream(db); /* terminate start scope write */
}
/*
 * top-level example code
 */
void
example_code(const char* ucisdb)
{
    ucisFileHandleT filehandle;
    ucisT db = ucis_OpenWriteStream(ucisdb);
    create_testdata(db,ucisdb);
    filehandle = create_filehandle(db,"test.sv");
    create_design_unit(db,"work.top",filehandle,1);
    create_instance(db,"top","work.top");
    create_statement(db,filehandle,1,6,1,17);
    create_statement(db,filehandle,1,8,1,0);
    create_statement(db,filehandle,1,9,2, 365);
    create_enum_toggle(db);
    create_covergroup(db,"cg",filehandle,3);
    create_coverpoint(db,"t",filehandle,4);
    create_coverpoint_bin(db,"auto[a]",filehandle,4,1,0,"a");
    create_coverpoint_bin(db,"auto[b]",filehandle,4,1,1,"b");
    ucis_WriteStreamScope(db); /* terminate coverpoint */
    ucis_WriteStreamScope(db); /* terminate covergroup */
    ucis_WriteStreamScope(db); /* terminate instance */
    printf("Writing UCIS file '%s'\n", ucisdb);
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
