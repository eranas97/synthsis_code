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
 *  UCDB Save Callback Example
 *
 *  The VPI model "mymodel" is just an inverter with a Verilog shell.
 *  The interesting part of the example is the installation of the UCDB save
 *  callback and the UCDB API write streaming code to create the UCDB data.
 *
 *  The UCDB data in this case is the same two-bin covergroup from the
 *  write-streaming example.
 *
 *  Note: the UCDB covergroup data model changed somewhat with Questa 6.4 to
 *  accommodate SV 2009 covergroup options.  Select the release with the
 *  QUESTA_RELEASE preprocessor #define.
 *  
 *****************************************************************************/
#include <stdlib.h>
#include <stdio.h>
#include "sv_vpi_user.h"
#include "mti.h"
#include "ucdb.h"

#define QUESTA_RELEASE 64   /* valid values: 63 64 */

int mymodel(), mymodel_setup();
void write_ucdb_data(ucdbT);

/*
 *  Register mymodel with simulator
 */
void register_mymodel()
{
    s_vpi_systf_data systf_data;
    systf_data.type = vpiSysFunc;
    systf_data.sysfunctype = vpiSysFuncSized;
    systf_data.tfname = "$mymodel";
    systf_data.calltf = mymodel;
    systf_data.compiletf = mymodel_setup;
    systf_data.sizetf = NULL;
    vpi_register_systf(&systf_data);
}

/*
 *  Implement $mymodel 
 */
int mymodel(char *unused)
{
    s_vpi_value value;
    vpiHandle systf_handle, arg_iter, arg_handle;

    systf_handle = vpi_handle(vpiSysTfCall,NULL);
    arg_iter = vpi_iterate(vpiArgument,systf_handle);
    arg_handle = vpi_scan(arg_iter);
    value.format = vpiIntVal;
    vpi_get_value(arg_handle,&value);
    value.value.integer = !value.value.integer;
    vpi_put_value(systf_handle,&value,NULL,vpiNoDelay);
    return 0;
}

/*
 *  UCDB Save Callback
 */
void
mymodel_ucdb_save(ucdbT db,
                  mtiRegionIdT region,
                  void* unused)
{
    vpi_printf("Saving UCDB data from VPI model ...\n");
    write_ucdb_data(db);
}

/*
 *  Register UCDB Save Callback
 */
int mymodel_setup(char* unused)
{
    vpiHandle systf_handle, scope_handle;
    char* scope_name;
    mtiRegionIdT FLI_scope_handle;

    /* Get name of enclosing scope through VPI */
    systf_handle = vpi_handle(vpiSysTfCall,NULL);
    scope_handle = vpi_handle(vpiScope,systf_handle);
    scope_name = vpi_get_str(vpiFullName,scope_handle);

    /* Convert to FLI region id type */
    FLI_scope_handle = mti_FindRegion(scope_name);
    scope_name = mti_GetRegionFullName(FLI_scope_handle);

    /* Install UCDB save callback */
    vpi_printf("Installing UCDB Save Callback for %s ...\n",scope_name);
    mti_AddUCDBSaveCB(FLI_scope_handle,mymodel_ucdb_save,NULL);
    return 0;
}

void (*vlog_startup_routines[])() = 
{
    register_mymodel,
    0
};


/******************************************************************************
 *  Code copied from write-streaming/create_ucdb.c
 *****************************************************************************/
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
 *  This is copied from example_code() in the write-streaming example
 */
void
write_ucdb_data(ucdbT db)
{
    ucdbFileHandleT filehandle;
    filehandle = create_filehandle(db,"test.sv");
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
}
