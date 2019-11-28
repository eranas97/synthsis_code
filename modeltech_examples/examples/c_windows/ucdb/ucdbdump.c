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
// UCDB dump utility to covert raw UCDB data into readible text data.
// Usage:
//       ucdbdump UCDB_file [-o dump_file ]
//
//       ** default output is stdout
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>

/* include UCDB API header */
#include "ucdb.h"

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

/*---------------------------------------------------------------------------
*   ud_PrintSourceInfo
*        - print source info
*---------------------------------------------------------------------------*/
void ud_PrintSourceInfo(FILE            *outFile,
                        ucdbT            db,
                        ucdbSourceInfoT  srcinfo,
                        int              isScope)
{
    const char* file = ucdb_GetFileName(db, &srcinfo.filehandle);

    if (isScope)
    {
       fprintf(outFile, "%-15s : ", "File info");
    }
    else
    {
       fprintf(outFile, "\t %-10s : ", "File info");
    }

    fprintf(outFile, "name = %s ", file ? file : "<none>");

    fprintf(outFile, "line = %d ", srcinfo.line);

    fprintf(outFile, "\n");
}

/*---------------------------------------------------------------------------
*   ud_PrintScopeType
*        - print scope type
*---------------------------------------------------------------------------*/
void ud_PrintScopeType(FILE*          outFile,
                       ucdbScopeTypeT scopeType)
{
    fprintf(outFile, "%-15s : ", "Type");

    switch (scopeType)
    {
    case UCDB_TOGGLE:
       fprintf(outFile, "UCDB_TOGGLE");
       break;

    case UCDB_BRANCH:
       fprintf(outFile, "UCDB_BRANCH");
       break;

    case UCDB_EXPR:
       fprintf(outFile, "UCDB_EXPR");
       break;

    case UCDB_COND:
       fprintf(outFile, "UCDB_COND");
       break;

    case UCDB_INSTANCE:
       fprintf(outFile, "UCDB_INSTANCE");
       break;

    case UCDB_PROCESS:
       fprintf(outFile, "UCDB_PROCESS");
       break;

    case UCDB_BLOCK:
       fprintf(outFile, "UCDB_BLOCK");
       break;

    case UCDB_FUNCTION:
       fprintf(outFile, "UCDB_FUNCTION");
       break;

    case UCDB_FORKJOIN:
       fprintf(outFile, "UCDB_FORKJOIN");
       break;

    case UCDB_GENERATE:
       fprintf(outFile, "UCDB_GENERATE");
       break;

    case UCDB_GENERIC:
       fprintf(outFile, "UCDB_GENERIC");
       break;

    case UCDB_CLASS:
       fprintf(outFile, "UCDB_CLASS");
       break;

    case UCDB_COVERGROUP:
       fprintf(outFile, "UCDB_COVERGROUP");
       break;

    case UCDB_COVERINSTANCE:
       fprintf(outFile, "UCDB_COVERINSTANCE");
       break;

    case UCDB_COVERPOINT:
       fprintf(outFile, "UCDB_COVERPOINT");
       break;

    case UCDB_CROSS:
       fprintf(outFile, "UCDB_CROSS");
       break;

    case UCDB_COVER:
       fprintf(outFile, "UCDB_COVER");
       break;

    case UCDB_ASSERT:
       fprintf(outFile, "UCDB_ASSERT");
       break;

    case UCDB_PROGRAM:
       fprintf(outFile, "UCDB_PROGRAM");
       break;

    case UCDB_PACKAGE:
       fprintf(outFile, "UCDB_PACKAGE");
       break;

    case UCDB_TASK:
       fprintf(outFile, "UCDB_TASK");
       break;

    case UCDB_INTERFACE:
       fprintf(outFile, "UCDB_INTERFACE");
       break;

    case UCDB_FSM:
       fprintf(outFile, "UCDB_FSM");
       break;

    case UCDB_FSM_STATES:
       fprintf(outFile, "UCDB_FSM_STATES");
       break;

    case UCDB_FSM_TRANS:
       fprintf(outFile, "UCDB_FSM_TRANS");
       break;

    case UCDB_TESTPLAN:
       fprintf(outFile, "UCDB_TESTPLAN");
       break;

    case UCDB_DU_MODULE:
       fprintf(outFile, "UCDB_DU_MODULE");
       break;

    case UCDB_DU_ARCH:
       fprintf(outFile, "UCDB_DU_ARCH");
       break;

    case UCDB_DU_PACKAGE:
       fprintf(outFile, "UCDB_DU_PACKAGE");
       break;

    case UCDB_DU_PROGRAM:
       fprintf(outFile, "UCDB_DU_PROGRAM");
       break;

    case UCDB_DU_INTERFACE:
       fprintf(outFile, "UCDB_DU_INTERFACE");
       break;

	case UCDB_GROUP:
	   fprintf(outFile, "UCDB_GROUP");
	   break;

    default:
       fprintf(outFile, "<unrecognized>");
       break;
    }

    fprintf(outFile, "\n");
}

/*---------------------------------------------------------------------------
*   ud_PrintSourceType
*        - print source details
*---------------------------------------------------------------------------*/
void ud_PrintSourceType(FILE        *outFile,
                        ucdbSourceT  sourceType)
{
    fprintf(outFile, "%-15s : ", "Source type");

    switch (sourceType)
    {
    case UCDB_VHDL:
        fprintf(outFile, "VHDL");
        break;

    case UCDB_VLOG:
        fprintf(outFile, "VERILOG");
        break;

    case UCDB_SV:
        fprintf(outFile, "SYSTEMVERILOG");
        break;

    case UCDB_SYSTEMC:
        fprintf(outFile, "SYSTEMC");
        break;

    case UCDB_PSL_VHDL:
        fprintf(outFile, "PSL_VHDL");
        break;

    case UCDB_PSL_VLOG:
        fprintf(outFile, "PSL_VLOG");
        break;

    case UCDB_PSL_SV:
        fprintf(outFile, "PSL_SV");
        break;

    case UCDB_PSL_SYSTEMC:
        fprintf(outFile, "PSL_SYSTEMC");
        break;

    case UCDB_E:
        fprintf(outFile, "E");
        break;

    case UCDB_VERA:
        fprintf(outFile, "VERA");
        break;

    case UCDB_NONE:
        fprintf(outFile, "NONE");
        break;

    case UCDB_OTHER:
        fprintf(outFile, "OTHER");
        break;

    case UCDB_SOURCE_ERROR:
        fprintf(outFile, "SOURCE_ERROR");
        break;

    default:
        fprintf(outFile, "<unrecognized>");
        break;
    }

    fprintf(outFile, "\n");
}

/*---------------------------------------------------------------------------
*   ud_PrintStatus
*        - print status
*---------------------------------------------------------------------------*/
void ud_PrintStatus(FILE            *outFile,
                    ucdbTestStatusT  testStatus)
{
    assert(outFile != NULL);

    fprintf(outFile, "%-15s : ", "Status");

    switch (testStatus)
    {
    case UCDB_TESTSTATUS_OK:
        fprintf(outFile, "OK");
        break;

    case UCDB_TESTSTATUS_WARNING:
        fprintf(outFile, "WARNING");
        break;

    case UCDB_TESTSTATUS_ERROR:
        fprintf(outFile, "ERROR");
        break;

    case UCDB_TESTSTATUS_FATAL:
        fprintf(outFile, "FATAL");
        break;

    case UCDB_TESTSTATUS_MISSING:
        fprintf(outFile, "MISSING");
        break;

    case UCDB_TESTSTATUS_MERGE_ERROR:
        fprintf(outFile, "MERGE_ERROR");
        break;

    default:
        fprintf(outFile, "<unrecognized>");
        break;
    }

    fprintf(outFile, "\n");
}

/*---------------------------------------------------------------------------
*   ud_PrintCoverFlags
*        - print cover flags
*---------------------------------------------------------------------------*/
void ud_PrintCoverFlags(FILE               *outFile,
                        ucdbFlagsT          flags,
                        ucdbCoverTypeT      type,
                        ucdbCoverDataValueT data,
                        int                 goal,
                        int                 weight,
                        int                 limit,
                        int                 bitlen)
{
    int isVector = 0;

    if (flags & UCDB_IS_VECTOR)
    {
        isVector = 1;
    }

    if (flags & UCDB_HAS_GOAL)
    {
        fprintf(outFile,"\t %-10s : %d\n", "Goal", goal);
    }

    if (flags & UCDB_HAS_WEIGHT)
    {
        fprintf(outFile,"\t %-10s : %d\n", "Weight", weight);
    }

    if (!isVector)
    {
        assert(!((flags & UCDB_IS_32BIT) && (flags & UCDB_IS_64BIT)));

        if (flags & UCDB_IS_32BIT)
        {
            fprintf(outFile, "\t %-10s : %d\n", "Count", data.int32);
        }
        else
        {
            fprintf(outFile,"\t %-10s : %ld\n", "Count", (long)(data.int64));
        }
    }
    else
    {
        int byte;
        int bytelen = ((bitlen/8) + ((bitlen%8) ? 1 : 0));
        fprintf(outFile,"\t %-10s : ", "Vector");
        for ( byte=0; byte<bytelen; byte++ ) {
            fprintf(outFile,"%02x ", data.bytevector[byte]);
        }
        fprintf(outFile,"\n");
    }
    if (flags & UCDB_HAS_LIMIT)
    {
         fprintf(outFile, "\t %-10s : %d\n", "Limit", limit);
    }

    if (flags & UCDB_EXCLUDE_PRAGMA)
    {
        assert(type & UCDB_CODE_COV);

        fprintf(outFile, "\t %-10s : %s\n", "Exclude", "pragma");
    }

    if (flags & UCDB_EXCLUDE_FILE)
    {
        assert(type & UCDB_CODE_COV);

        fprintf(outFile, "\t %-10s : %s\n", "Exclude", "file");
    }

    if (flags & UCDB_EXCLUDE_AUTO)
    {
        assert(type & UCDB_CODE_COV);

        fprintf(outFile, "\t %-10s : %s\n", "Exclude", "auto");
    }

    if (flags & UCDB_LOG_ON)
    {
        assert((type & UCDB_ASSERTIONBINS) ||
               (type & UCDB_COVERBIN));

        fprintf(outFile, "\t %-10s : 1\n", "Log");
    }

    if (flags & UCDB_ENABLED)
    {
        fprintf(outFile, "\t %-10s : 1\n", "Enabled");
    }

    if (flags & UCDB_HAS_ACTION)
    {
        assert((type & UCDB_ASSERTIONBINS) ||
               (type & UCDB_COVERBIN));

        fprintf(outFile, "\t %-10s : 1\n", "Has Action");
    }

    if (flags & UCDB_USERFLAGS)
    {
        fprintf(outFile, "\t %-10s : 1\n", "User flags");
    }

    if (flags) {
        fprintf(outFile, "\t %-10s : 0x%08x\n", "Flags", flags);
    }
}

/*---------------------------------------------------------------------------
*   ud_PrintCoverType
*        - print cover type
*---------------------------------------------------------------------------*/
void ud_PrintCoverType(FILE               *outFile,
                       ucdbCoverTypeT      type)
{
    fprintf(outFile, "\t %-10s : ", "Type");

    /* ILLEGAL/IGNORE BIN can be DEFAULT BIN too, so first check the special case */

    if (type & UCDB_DEFAULTBIN) {
        if (type & UCDB_IGNOREBIN) {
            fprintf(outFile, "UCDB_IGNOREBIN_AND_DEFAULTBIN");
            fprintf(outFile, "\n"); 
            return;
        }
        if (type & UCDB_ILLEGALBIN) {
            fprintf(outFile, "UCDB_ILLEGALBIN_AND_DEFAULTBIN");
            fprintf(outFile, "\n"); 
            return;
        }
        if (type & UCDB_CVGBIN) {
            fprintf(outFile, "UCDB_DEFAULTBIN");
            fprintf(outFile, "\n"); 
            return;
        }
    }

    switch(type)
    {
    case UCDB_CVGBIN:
       fprintf(outFile, "UCDB_CVGBIN");
       break;

    case UCDB_COVERBIN:
       fprintf(outFile, "UCDB_COVERBIN");
       break;

    case UCDB_ASSERTBIN:
       fprintf(outFile, "UCDB_ASSERTBIN");
       break;

    case UCDB_SCBIN:
       fprintf(outFile, "UCDB_SCBIN");
       break;

    case UCDB_ZINBIN:
       fprintf(outFile, "UCDB_ZINBIN");
       break;

    case UCDB_STMTBIN:
       fprintf(outFile, "UCDB_STMTBIN");
       break;

    case UCDB_BRANCHBIN:
       fprintf(outFile, "UCDB_BRANCHBIN");
       break;

    case UCDB_EXPRBIN:
       fprintf(outFile, "UCDB_EXPRBIN");
       break;

    case UCDB_CONDBIN:
       fprintf(outFile, "UCDB_CONDBIN");
       break;

    case UCDB_TOGGLEBIN:
       fprintf(outFile, "UCDB_TOGGLEBIN");
       break;

    case UCDB_PASSBIN:
       fprintf(outFile, "UCDB_PASSBIN");
       break;

    case UCDB_FSMBIN:
       fprintf(outFile, "UCDB_FSMBIN");
       break;

    case UCDB_USERBIN:
       fprintf(outFile, "UCDB_USERBIN");
       break;

    case UCDB_COUNT:
       fprintf(outFile, "UCDB_COUNT");
       break;

    case UCDB_FAILBIN:
       fprintf(outFile, "UCDB_FAILBIN");
       break;

    case UCDB_VACUOUSBIN:
       fprintf(outFile, "UCDB_VACUOUSBIN");
       break;

    case UCDB_DISABLEDBIN:
       fprintf(outFile, "UCDB_DISABLEDBIN");
       break;

    case UCDB_ATTEMPTBIN:
       fprintf(outFile, "UCDB_ATTEMPTBIN");
       break;

    case UCDB_ACTIVEBIN:
       fprintf(outFile, "UCDB_ACTIVEBIN");
       break;

    case UCDB_IGNOREBIN:
       fprintf(outFile, "UCDB_IGNOREBIN");
       break;

    case UCDB_ILLEGALBIN:
       fprintf(outFile, "UCDB_ILLEGALBIN");
       break;

    case UCDB_DEFAULTBIN:
       fprintf(outFile, "UCDB_DEFAULTBIN");
       break;

    case UCDB_PEAKACTIVEBIN:
       fprintf(outFile, "UCDB_PEAKACTIVEBIN");
       break;

    default:
       fprintf(outFile, "UNKNOWN (");
	   fprintf(outFile, LLUSTR, type);
	   fprintf(outFile, ")");
    }

    fprintf(outFile, "\n");
}

/*---------------------------------------------------------------------------
*   ud_PrintFlags
*        - print flags for a scope
*---------------------------------------------------------------------------*/
void ud_PrintFlags(FILE               *outFile,
                   ucdbFlagsT          flags)
{
    fprintf(outFile, "%-15s : 0x%08x\n", "Flags", flags);
}

/*---------------------------------------------------------------------------
*   ud_PrintTestData
*        - print test data
*---------------------------------------------------------------------------*/
void ud_PrintTestData(FILE            *outFile,
                      const char      *fileName,
                      const char      *name,
                      ucdbTestStatusT  testStatus,
                      double           simtime,
                      const char      *simtimeUnits,
                      double           cputime,
                      const char      *seed,
                      const char      *testArgs,
                      const char      *vsimArgs,
                      const char      *comment,
                      int              compulsory,
                      const char      *date,
                      const char      *userid)
{
    fprintf(outFile, "\n------------ TEST -------------------------\n");
    fprintf(outFile, "%-15s : %s\n", "Name", name);
    fprintf(outFile, "%-15s : %s\n", "File name", fileName);

    ud_PrintStatus(outFile, testStatus);

    fprintf(outFile, "%-15s : %f %s\n", "Simulation time",
                       simtime, simtimeUnits);
    fprintf(outFile, "%-15s : %d\n", "Compulsory", compulsory);
    if (seed != NULL) {
        fprintf(outFile, "%-15s : %s\n", "Seed", seed);
    } else {
        fprintf(outFile, "%-15s : NONE\n", "Seed");
    }
    fprintf(outFile, "%-15s : %s\n", "Test args", testArgs?testArgs:"(null)");
    fprintf(outFile, "%-15s : %s\n", "Vsim args", vsimArgs);
    fprintf(outFile, "%-15s : %s\n", "Comment", comment?comment:"(null)");
    fprintf(outFile, "%-15s : %s\n", "Date", date);
    fprintf(outFile, "%-15s : %s\n", "Userid", userid);
}

/*---------------------------------------------------------------------------
*   ud_PrintCoverData
*        - print cover data
*---------------------------------------------------------------------------*/
void ud_PrintCoverData(FILE               *outFile,
                       ucdbT               db,
                       char               *name,
                       ucdbCoverTypeT      type,
                       ucdbFlagsT          flags,
                       ucdbCoverDataValueT data,
                       int                 goal,
                       int                 weight,
                       int                 limit,
                       int                 bitlen,
                       ucdbSourceInfoT     srcinfo)
{
    fprintf(outFile, "\nCover item - \n");

    if (type != UCDB_STMTBIN)
    {
       assert(name != NULL);

       fprintf(outFile, "\t %-10s : %s\n", "Name", name);
    }

    ud_PrintCoverType(outFile, type);

    ud_PrintSourceInfo(outFile, db, srcinfo, 0);

    ud_PrintCoverFlags(outFile, flags, type, data, goal, weight, limit,
                       bitlen);
}

/*---------------------------------------------------------------------------
*   ud_PrintDU
*        - print design unit
*---------------------------------------------------------------------------*/
void ud_PrintDU(FILE*           outFile,
                ucdbT           db,
                const char*     name,
                ucdbScopeTypeT  scopeType,
                ucdbSourceT     sourceType,
                ucdbSourceInfoT srcinfo,
                ucdbFlagsT      flags)
{
    fprintf(outFile, "\n------------- DESIGN UNIT ------------------\n");

    fprintf(outFile, "%-15s : %s\n", "Name", name);

    ud_PrintScopeType(outFile, scopeType);

    ud_PrintSourceType(outFile, sourceType);

    ud_PrintSourceInfo(outFile, db, srcinfo, 1);

    ud_PrintFlags(outFile, flags);
}

/*---------------------------------------------------------------------------
*   ud_PrintAttribute
*        - print attributes
*---------------------------------------------------------------------------*/
void ud_PrintAttribute(FILE           *outFile,
                       const char     *key,
                       ucdbAttrValueT*  value)
{
    fprintf(outFile, "Attribute: name = %s ", key);

    switch (value->type)
    {
    case UCDB_ATTR_INT:
       fprintf(outFile, "int = %d", value->u.ivalue);
       break;

    case UCDB_ATTR_FLOAT:
       fprintf(outFile, "float = %f", value->u.fvalue);
       break;

    case UCDB_ATTR_DOUBLE:
       fprintf(outFile, "double = %f", value->u.dvalue);
       break;

    case UCDB_ATTR_STRING:
       fprintf(outFile, "string = \"%s\"", value->u.svalue?value->u.svalue:"(null)");
       break;

    case UCDB_ATTR_MEMBLK:
       fprintf(outFile, "mem_block size = %d ", value->u.mvalue.size);
       if (value->u.mvalue.size > 0) {
          int i;
          fprintf(outFile,"/ ");
          for ( i=0; i<value->u.mvalue.size; i++ )
             fprintf(outFile, "%02x ", value->u.mvalue.data[i]);
       }
       break;
    case UCDB_ATTR_INT64:
       fprintf(outFile, "int64 = ");
       fprintf(outFile, LLDSTR, value->u.i64value);
       break;

    default:
      assert(0);
    }

    fprintf(outFile, "\n");
}

/*---------------------------------------------------------------------------
*   ud_ProcessAttributes
*        - process attributes
*---------------------------------------------------------------------------*/
void ud_ProcessAttributes(FILE       *outFile,
                          ucdbT      *db,
                          void       *obj,
                          int         coverindex)
{
    const char*    key = NULL;
    ucdbAttrValueT value;

    while ((key = ucdb_AttrGetNext(db, obj, coverindex, key, &value)))
    {
        ud_PrintAttribute(outFile, key, &value);
    }
}

/*---------------------------------------------------------------------------
*   ud_PrintTags
*        - prints error tag
*---------------------------------------------------------------------------*/
void ud_PrintTags(FILE        *outFile,
                  ucdbT       *db,
                  ucdbScopeT  *scope)
{
    int           i;
    int           status;
    int           numtags;
    const char*   tag;

    numtags = ucdb_GetScopeNumTags(db, scope);

    for (i = 0; i < numtags; i++)
    {
        status = ucdb_GetScopeIthTag(db, scope, i, &tag);

        assert(status == 0);

        fprintf(outFile, "Tag: %s\n", tag);
    }
}

static const char* 
ucdb_GroupKind2Str(ucdbGroupKind kind)
{
	const char* groupKindString;

	switch(kind) {
	case UCDB_GROUP_BASIC:
        groupKindString = "BASIC";
	    break;
    case UCDB_GROUP_UNPACKED_STRUCT:
        groupKindString = "UNPACKED_STRUCT";
	    break;
    case UCDB_GROUP_UNPACKED_UNION:
        groupKindString = "UNPACKED_UNION";
	    break;
    case UCDB_GROUP_UNPACKED_ARRAY:
        groupKindString = "UNPACKED_ARRAY";
	    break;
    case UCDB_GROUP_ASSOC_ARRAY:
        groupKindString = "ASSOC_ARRAY";
	    break;
    case UCDB_GROUP_PACKED_STRUCT:
        groupKindString = "PACKED_STRUCT";
	    break;
    case UCDB_GROUP_PACKED_UNION:
        groupKindString = "PACKED_UNION";
	    break;
    case UCDB_GROUP_PACKED_ARRAY:
        groupKindString = "PACKED_ARRAY";
	    break;
	default:
		/* This should not happen */
        groupKindString = "UNKNOWN";
	}
	return groupKindString;
}

/*---------------------------------------------------------------------------
*	ud_PrintGroupInfo
*		 - prints toggle info
*---------------------------------------------------------------------------*/
static void 
ud_PrintGroupInfo(FILE*         outFile,
			      ucdbGroupKind kind,               /* The group kind */
			      int           numberOfRangePairs, /* Used only for ordered groups */
			      int*          rangePairs)         /* Used only for ordered groups */
{
	const char* groupKindString;

    groupKindString = ucdb_GroupKind2Str(kind);

	fprintf(outFile, "%-15s : %s\n", "Group Kind", groupKindString);

	if ((kind & UCDB_GROUP_MASK_ORDERED) == UCDB_GROUP_MASK_ORDERED) {
		int count;

        if (numberOfRangePairs <= 0) {
			fprintf(outFile, "%-15s : <UNDETERMINED>\n", "Range Pairs");
        } else {
			fprintf(outFile, "%-15s : %d\n", "Range Pairs", numberOfRangePairs);
			for (count=0; count<numberOfRangePairs; count++) {
				int index;

				index = count+count;
				fprintf(outFile, "%-15s : %d-%d\n", "Range Pair", rangePairs[index], rangePairs[index+1]);
			}
		}
	}
}

/*---------------------------------------------------------------------------
*   ud_PrintToggleInfo
*        - prints toggle info
*---------------------------------------------------------------------------*/
void ud_PrintToggleInfo(FILE           *outFile,
                        const char     *canonicalName,
                        ucdbToggleTypeT toggleType,
                        ucdbToggleDirT  toggleDir)
{
    const char* toggleTypeString = NULL;
    const char* toggleDirString = NULL;

    fprintf(outFile, "%-15s : %s\n", "Canonical Name", 
            canonicalName ? canonicalName : "");

    switch(toggleType) {
    case UCDB_TOGGLE_ENUM:           toggleTypeString = "ENUM"; break;
    case UCDB_TOGGLE_INT:            toggleTypeString = "INT"; break; 
    case UCDB_TOGGLE_REG_SCALAR:     toggleTypeString = "REG_SCALAR"; break; 
    case UCDB_TOGGLE_REG_SCALAR_EXT: toggleTypeString = "REG_SCALAR_EXT";
                                     break;
    case UCDB_TOGGLE_SCALAR:         toggleTypeString = "SCALAR"; break; 
    case UCDB_TOGGLE_SCALAR_EXT:     toggleTypeString = "SCALAR_EXT"; break; 
    case UCDB_TOGGLE_REAL:           toggleTypeString = "REAL"; break; 
    }

    fprintf(outFile, "%-15s : %s\n", "Toggle Type", toggleTypeString);

    switch(toggleDir) {
    case UCDB_TOGGLE_INTERNAL:       toggleDirString = "INTERNAL"; break;
    case UCDB_TOGGLE_IN:             toggleDirString = "IN"; break;
    case UCDB_TOGGLE_OUT:            toggleDirString = "OUT"; break;
    case UCDB_TOGGLE_INOUT:          toggleDirString = "INOUT"; break;
    }

    fprintf(outFile, "%-15s : %s\n", "Toggle Dir", toggleDirString);
}

/*---------------------------------------------------------------------------
*   ud_error_handler
*        - generic error handler
*---------------------------------------------------------------------------*/
void ud_error_handler(void       *ud_data,
                      ucdbErrorT *errorInfo)
{
    assert(ud_data == NULL);

    fprintf(stderr, "%s\n", errorInfo->msgstr);

    if (errorInfo->severity == UCDB_MSG_ERROR)
    {
        exit(1);
    }
}

/*---------------------------------------------------------------------------
*	ud_PrintScope
*		 - print scope
*---------------------------------------------------------------------------*/
static void ud_PrintScope(FILE			   *outFile,
				   ucdbT			db,
				   ucdbScopeT		scope,
				   const char	   *name,
				   ucdbScopeTypeT	scopeType,
				   ucdbSourceT		sourceType,
				   int				weight,
				   ucdbFlagsT		flags)
{
	ucdbSourceInfoT sourceinfo;
	int cvp;
	int numcvps;
    ucdbScopeT duscope;

	if (scopeType & UCDB_HDL_INST_SCOPE)
	{
		fprintf(outFile, "\n------------- INSTANCE SCOPE ----------------\n");
	}
	else if (scopeType & UCDB_CODE_COV_SCOPE)
	{
		fprintf(outFile, "\nCode Coverage Scope - \n");
	}
	else if (scopeType & (UCDB_COVERGROUP | UCDB_COVERINSTANCE
						| UCDB_COVERPOINT | UCDB_CROSS | UCDB_COVER))
	{
		fprintf(outFile, "\nFunctional Coverage Scope - \n");
	}
	else if (scopeType & UCDB_ASSERT)
	{
		fprintf(outFile, "\nAssertion Scope - \n");
	}
	else if (scopeType & UCDB_GROUP)
	{
		fprintf(outFile, "\nGroup Scope - \n");
	}
	else
	{
		fprintf(outFile, "\nScope - \n");
	}

	fprintf(outFile, "%-15s : %s\n", "Name", name);

	ud_PrintScopeType(outFile, scopeType);

	ud_PrintSourceType(outFile, sourceType);

	switch (scopeType) {
	case UCDB_GROUP:
		{
			ucdbGroupKind kind;               /* The group kind */
			int           numberOfRangePairs; /* Used only for ordered groups */
			int*          rangePairs;         /* Used only for ordered groups */

			ud_PrintFlags(outFile, flags);
			ucdb_GetGroupInfo(db, scope, &kind, NULL, &numberOfRangePairs, &rangePairs);
			ud_PrintGroupInfo(outFile, kind, numberOfRangePairs, rangePairs);
		}
		break;
	case UCDB_CROSS:
	    ucdb_GetScopeSourceInfo(db, scope, &sourceinfo);
	    ud_PrintSourceInfo(outFile, db, sourceinfo, 1);
		/*
		 *	Print the names of the coverpoints that were crossed.
		 */
		(void)ucdb_GetNumCrossedCvps(db,scope,&numcvps);
		fprintf(outFile, "%-15s : ", "Coverpoints");
		for ( cvp=0; cvp<numcvps; cvp++ ) {
			fprintf(outFile, "%s ", 
					ucdb_GetIthCrossedCvpName(db,scope,cvp));
		}
		fprintf(outFile,"\n");
		if (weight >= 0)
		{
		   fprintf(outFile, "%-15s : %d\n", "Weight", weight);
		}
	    ud_PrintFlags(outFile, flags);
		break;
	case UCDB_INSTANCE:
	case UCDB_PROGRAM:
	case UCDB_PACKAGE:
	case UCDB_INTERFACE:
	    ucdb_GetScopeSourceInfo(db, scope, &sourceinfo);
	    ud_PrintSourceInfo(outFile, db, sourceinfo, 1);
		duscope = ucdb_GetInstanceDU(db,scope);
		fprintf(outFile, "%-15s : ", "DU Scope");
		if (duscope) {
			fprintf(outFile, "%s\n", ucdb_GetScopeName(db,duscope));
		} else {
			fprintf(outFile, "(none: ill-formed UCDB)\n");
		}
		if (weight >= 0)
		{
		   fprintf(outFile, "%-15s : %d\n", "Weight", weight);
		}
	    ud_PrintFlags(outFile, flags);
		break;
	case UCDB_ASSERT:
		{
			ucdbAssertFormalModeT formal_mode;
			int proof_radius;

			ucdb_GetScopeSourceInfo(db, scope, &sourceinfo);
			ud_PrintSourceInfo(outFile, db, sourceinfo, 1);
			if (weight >= 0)
			{
			   fprintf(outFile, "%-15s : %d\n", "Weight", weight);
			}
			ud_PrintFlags(outFile, flags);

			if (ucdb_GetFormalMode(db, scope, &formal_mode) != 0) {
				/* Uninitialized data -- initialize it! */
				formal_mode = UCDB_FORMAL_NONE;
			}
			if (ucdb_GetProofRadius(db, scope, &proof_radius) != 0) {
				/* Uninitialized data -- initialize it! */
				proof_radius = -1;
			}

			switch(formal_mode) {
			case UCDB_FORMAL_INCONCLUSIVE:
				fprintf(outFile, "%-15s : %s\n", "Formal kind", "inconclusive");
				break;
			case UCDB_FORMAL_FAILURE:
				fprintf(outFile, "%-15s : %s\n", "Formal kind", "failure");
				break;
			case UCDB_FORMAL_PROOF:
				fprintf(outFile, "%-15s : %s\n", "Formal kind", "proof");
				break;
			case UCDB_FORMAL_VACUOUS:
				fprintf(outFile, "%-15s : %s\n", "Formal kind", "vacuous");
				break;
			case UCDB_FORMAL_ASSUMPTION:
				fprintf(outFile, "%-15s : %s\n", "Formal kind", "assume");
				break;
			case UCDB_FORMAL_CONFLICT:
				fprintf(outFile, "%-15s : %s\n", "Formal kind", "conflict");
				break;
			case UCDB_FORMAL_NONE:
			default:
				break;
			}

			/* Formal proof radius */
			if (proof_radius >= 0) {
				 fprintf(outFile, "%-15s : %d\n", "Formal proof radius", proof_radius);
			}
		}
	    break;
	case UCDB_TOGGLE:
		{
			const char* canonicalName;
			ucdbToggleTypeT toggleType;
			ucdbToggleDirT toggleDir;

			ucdb_GetScopeSourceInfo(db, scope, &sourceinfo);
			ud_PrintSourceInfo(outFile, db, sourceinfo, 1);
			if (weight >= 0)
			{
			   fprintf(outFile, "%-15s : %d\n", "Weight", weight);
			}
			ud_PrintFlags(outFile, flags);

			ucdb_GetToggleInfo(db, scope, &canonicalName, &toggleType, &toggleDir);

			ud_PrintToggleInfo(outFile, canonicalName, toggleType, toggleDir);
		}
	    break;
	default:
	    ucdb_GetScopeSourceInfo(db, scope, &sourceinfo);
	    ud_PrintSourceInfo(outFile, db, sourceinfo, 1);
		if (weight >= 0)
		{
		   fprintf(outFile, "%-15s : %d\n", "Weight", weight);
		}
	    ud_PrintFlags(outFile, flags);
	}
}

/*---------------------------------------------------------------------------
*   ud_initdb_cb
*        - callback function for database initialization
*---------------------------------------------------------------------------*/
void ud_initdb_cb(FILE        *outFile,
                  ucdbT       *db,
                  ucdbScopeT  *obj)
{
    /* Print global attributes */
    ud_ProcessAttributes(outFile, db, NULL, -1);
}

/*---------------------------------------------------------------------------
*   ud_test_cb
*        - callback function for tests
*---------------------------------------------------------------------------*/
void ud_test_cb(FILE       *outFile,
                ucdbT      *db,
                ucdbTestT  *test)
{
    int             status;
    const char*     fileName;
    const char*     name;
    ucdbTestStatusT testStatus;
    double          simtime;
    const char*     simtimeUnits;
    double          cputime;
    const char*     seed;
    const char*     testArgs;
    const char*     vsimArgs;
    const char*     comment;
    int             compulsory;
    const char*     date;
    const char*     userid;

    assert(outFile != NULL);
    assert(db != NULL);
    assert(test != NULL);

    status = ucdb_GetTestData(db,
                              test,
                              &fileName,
                              &name,
                              &testStatus,
                              &simtime,
                              &simtimeUnits,
                              &cputime,
                              &seed,
                              &testArgs,
                              &vsimArgs,
                              &comment,
                              &compulsory,
                              &date,
                              &userid
                             );
    assert(status == 0);

    ud_PrintTestData(outFile,
                     fileName,
                     name,
                     testStatus,
                     simtime,
                     simtimeUnits,
                     cputime,
                     seed,
                     testArgs,
                     vsimArgs,
                     comment,
                     compulsory,
                     date,
                     userid
                    );

    ud_ProcessAttributes(outFile, db, test, -1);
}

/*---------------------------------------------------------------------------
*   ud_du_cb
*        - callback function for scopes
*---------------------------------------------------------------------------*/
void ud_du_cb(FILE        *outFile,
              ucdbT       *db,
              ucdbScopeT  *du)
{
    ucdbSourceT     sourceType;
    ucdbScopeTypeT  scopeType;
    const char*     name;
    ucdbSourceInfoT srcinfo;
    ucdbFlagsT      flags;

    name = ucdb_GetScopeName(db, du);

    scopeType =  ucdb_GetScopeType(db, du);

    sourceType = ucdb_GetScopeSourceType(db, du);

    flags = ucdb_GetScopeFlags(db, du);

    ucdb_GetScopeSourceInfo(db, du, &srcinfo);

    ud_PrintDU(outFile, db, name, scopeType, sourceType, srcinfo, flags);

    ud_ProcessAttributes(outFile, db, du, -1);
}

/*---------------------------------------------------------------------------
*   ud_scope_start_cb
*        - callback function for HDL and Coverage scopes
*---------------------------------------------------------------------------*/
void ud_scope_start_cb(FILE          *outFile,
                       ucdbT       *db,
                       ucdbScopeT *scope)
{
    ucdbScopeTypeT  scopeType;
    int             weight;
    const char*     name;
    ucdbFlagsT      flags;
    ucdbSourceT     sourceType;

    assert(ucdb_GetScopeName(db, scope) != NULL);

    name = ucdb_GetScopeHierName(db, scope);

    scopeType =  ucdb_GetScopeType(db, scope);

    weight = ucdb_GetScopeWeight(db, scope);

    flags = ucdb_GetScopeFlags(db, scope);

    sourceType = ucdb_GetScopeSourceType(db, scope);

    ud_PrintScope(outFile, db, scope, name, scopeType, sourceType, weight, flags);

    ud_ProcessAttributes(outFile, db, scope, -1);

    ud_PrintTags(outFile, db, scope);
}

/*---------------------------------------------------------------------------
*   ud_coveritem_cb
*        - callback function for coveritem
*---------------------------------------------------------------------------*/
void ud_coveritem_cb(FILE       *outFile,
                     ucdbT        *db,
                     ucdbScopeT    *scope,
                     int         cvindex)
{
    char*                 name;
    ucdbCoverDataT        cvdata;
    ucdbSourceInfoT        srcinfo;

    ucdb_GetCoverData(db, scope, cvindex, &name, &cvdata, &srcinfo);

    ud_PrintCoverData(outFile,
                      db,
                      name,
                      cvdata.type,
                      cvdata.flags,
                      cvdata.data,
                      cvdata.goal,
                      cvdata.weight,
                      cvdata.limit,
                      cvdata.bitlen,
                      srcinfo);

    ud_ProcessAttributes(outFile, db, scope, cvindex);
}

/*---------------------------------------------------------------------------
*   ud_read_cb
*        - callback function for read streaming mode.
*---------------------------------------------------------------------------*/
ucdbCBReturnT ud_read_cb(void          *userData,
                         ucdbCBDataT  *cbData)
{
    ucdbT db  = cbData->db;
    void* obj = cbData->obj;

    FILE* outFile = (FILE*) userData;

    switch (cbData->reason)
    {
    case UCDB_REASON_TEST:
        ud_test_cb(outFile, db, obj);
        break;

    case UCDB_REASON_DU:
        ud_du_cb(outFile, db, obj);
        break;

    case UCDB_REASON_SCOPE:
        ud_scope_start_cb(outFile, db, obj);
        break;

    case UCDB_REASON_CVBIN:
        ud_coveritem_cb(outFile, db, obj, cbData->coverindex);
        break;

    case UCDB_REASON_ENDSCOPE:
        break;
    case UCDB_REASON_INITDB:
        ud_initdb_cb(outFile, db, obj);
        break;

    default:
        break;
    }

    return UCDB_SCAN_CONTINUE;
}

/*---------------------------------------------------------------------------
*    main
*       - process arguments
*       - register read streaming mode callback function
*       - open database in read streaming mode
*---------------------------------------------------------------------------*/
int main(int    argc,
         char **argv)
{
    char* outFileName   = NULL;
    char* inputFileName = NULL;
    FILE* outFile       = NULL;
    int   i;

    for (i = 1; i < argc; i++)
    {
        switch (*argv[i])
        {
        case '-':
             if (strcmp(argv[i], "-o") == 0)
             {
                 outFileName = argv[++i];

                 outFile = fopen(outFileName,"w");

                 if (outFile == NULL)
                 {
                     fprintf(stderr, "Error opening %s\n", outFileName);
                     exit(1);
                 }
            }
            else
            {
                 fprintf(stderr, "Illegal option name %s\n", argv[i]);
            }
            break;
        default:
            inputFileName = argv[i];
        }
    }

    if (outFile == NULL)
    {
        outFile = stdout;
    }

    ucdb_RegisterErrorHandler(ud_error_handler, NULL);

    ucdb_OpenReadStream(inputFileName, ud_read_cb, outFile);

    if (outFile != stdout)
    {
        fclose(outFile);
    }

    return 0;
}
