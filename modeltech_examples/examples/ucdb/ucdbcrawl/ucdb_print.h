 /*******************************************************************************
 *
 * Unified Coverage Database API Extension: ucdb_Print Functions
 *
 * Copyright 2006-2016 Mentor Graphics Corporation
 *
 * All Rights Reserved.
 *
 * THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
 * PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
 * LICENSE TERMS.
 *
 ******************************************************************************/
#ifndef UCDB_PRINT_H
#define UCDB_PRINT_H

#ifdef __cplusplus
extern "C" {
#endif

#include "ucdb.h"
#include <stdio.h>

#if defined(_MSC_VER) || defined(_WIN64)
	#define LLOSTR "%I64o"
	#define LLDSTR "%I64d"
	#define LLUSTR "%I64u"
	#define LLXSTR "%I64x"
#elif defined(_LP64) || defined(__LP64__) || defined(__64BIT__)
	#define LLOSTR "%lo"
    #define LLDSTR "%ld"
	#define LLUSTR "%lu"
	#define LLXSTR "%lx"
#else
	#define LLOSTR "%llo"
    #define LLDSTR "%lld"
	#define LLUSTR "%llu"
	#define LLXSTR "%llx"
#endif

/*-----------------------------------------------------------------------------
 *	Simple print functions for UCDB objects
 *  Requires ucdb.h header
 *---------------------------------------------------------------------------*/
/*
 *  ucdb_PrintScope
 *  Print a simple dump of scope contents to the given file descriptor.
 */
void
ucdb_PrintScope(
    ucdbT               db,
    ucdbScopeT          scope,      /* scope to print */
    FILE*               output,     /* stdout if NULL */
    ucdbSelectFlagsT    flags,      /* affects what can appear to output */
    int                 recurse,    /* descend to child scopes and covers */
	ucdbScopeTypeT      scope_mask, /* scope types to print if recurse==1 */
	ucdbCoverTypeT      cover_mask);/* cover types to print if recurse==1 */

/*
 *  ucdb_PrintCover
 *  Print a simple dump of coveritem contents to the given file descriptor
 *	Note: for a STMTBIN, which has no name, the UCDB_SELECT_SOURCEINFO flag is
 *	always asserted.
 */
void
ucdb_PrintCover(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex, /* index of coveritem in parent */
    FILE*               output,     /* stdout if NULL */
    ucdbSelectFlagsT    flags);     /* affects what can appear to output */

/*
 *  ucdb_PrintAttr
 *  Print a simple dump of an attribute to the given file descriptor
 */
void
ucdb_PrintAttr(
    ucdbT           db,
    void*           obj,            /* ucdbScopeT, ucdbTestT, or NULL */
    int             coverindex,     /* obj is ucdbScopeT: -1 for scope, valid index
                                       for coveritem */
    const char*     key,            /* attribute key string */
    FILE*           output);        /* stdout if NULL */

/*
 *  ucdb_PrintTestData
 *  Print a simple dump of a test data record to the given file descriptor.
 */
void
ucdb_PrintTestData(
    ucdbT               db,
    ucdbTestT           testdata,   /* test data record handle */
    FILE*               output,     /* stdout if NULL */
    ucdbSelectFlagsT    flags);     /* select attributes, tags etc. */

#ifdef __cplusplus
}
#endif

#endif
