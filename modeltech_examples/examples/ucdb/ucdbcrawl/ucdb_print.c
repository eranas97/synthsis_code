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

#include "ucdb_print.h"

/*------------------------------------------------------------------------------
 *  Common utilities
 *----------------------------------------------------------------------------*/
#define MAX_INDENT 128
#define INDENT_PER_LEVEL 2
static char indentation[MAX_INDENT+1];
static int prev_num_spaces = -1;
/*
 *  indent(): return a string with the number of spaces corresponding to the
 *  indentation level, which corresponds to levels deep in hierarchy in
 *  recursion.
 */
static const char*
indent(int level)
{
    int num_spaces = INDENT_PER_LEVEL*level;
    if (prev_num_spaces < 0) {
        /* This means our indentation string hasn't been filled with blanks
         * yet. */
        int i;
        for ( i=0; i<MAX_INDENT; i++ )
            indentation[i] = ' ';
        /* And start with a 0-length indentation string: */
        indentation[prev_num_spaces=0] = '\0';
    }

    if (num_spaces > MAX_INDENT) {
        num_spaces = MAX_INDENT;
    }
    if (num_spaces != prev_num_spaces) {
        indentation[prev_num_spaces] = ' ';
        indentation[prev_num_spaces=num_spaces] = '\0';
    }
    return indentation;
}

/*
 *  Print attributes as a list.
 */
#define MAX_CHARS_PER_LINE 120
static void
ucdb_print_attributes(ucdbT         db,
                      ucdbScopeT    scope,
                      int           coverindex,
                      FILE*         output,
                      int           level)
{
    const char* key = NULL;
    ucdbAttrValueT value;
    int chars_printed = 0;
    int printed_attr_to_line = 0;
	int attr_found = 0;
	int byte;
    while ((key = ucdb_AttrGetNext(db,scope,coverindex,key,&value))) {
		if (!attr_found) {
			chars_printed += fprintf(output,"%s",indent(level));
			attr_found = 1;
		} else if (chars_printed > MAX_CHARS_PER_LINE) {
			chars_printed = fprintf(output,"\n%s",indent(level));
			printed_attr_to_line = 0;
        }
        if (printed_attr_to_line) {
            chars_printed += fprintf(output," ");
        }
        chars_printed += fprintf(output,"%s=",key);
        switch(value.type) {
        case UCDB_ATTR_INT:
            chars_printed += fprintf(output,"%d",value.u.ivalue);
            break;
        case UCDB_ATTR_FLOAT:
            chars_printed += fprintf(output,"%f",value.u.fvalue);
            break;
        case UCDB_ATTR_DOUBLE:
            chars_printed += fprintf(output,"%lf",value.u.dvalue);
            break;
        case UCDB_ATTR_STRING:
            chars_printed += fprintf(output,"\"%s\"",
                                     value.u.svalue ? value.u.svalue : "(null)");
            break;
        case UCDB_ATTR_MEMBLK:
            {
                for ( byte=0; byte<value.u.mvalue.size; byte++ )
                    chars_printed += fprintf(output,"%02x",
                                             value.u.mvalue.data[byte]);
            }
            break;
        case UCDB_ATTR_INT64:
            chars_printed += fprintf(output,LLDSTR,value.u.i64value);
            break;

        default:
            chars_printed += fprintf(output,"<ERROR>");
        }
        printed_attr_to_line = 1;

    } /* end while ucdb_AttrGetNext */

	if (attr_found)
		fprintf(output,"\n");
}


/*------------------------------------------------------------------------------
 *  PrintCover
 *----------------------------------------------------------------------------*/
/*
 *  Convert cover data type to a string
 */
static char*
ucdb_cover_type_2string(ucdbCoverTypeT type)
{
    if (type & UCDB_DEFAULTBIN) {
        if (type & UCDB_IGNOREBIN) {
            return "IGNORE_DEFAULTBIN";
        }
        if (type & UCDB_ILLEGALBIN) {
            return "ILLEGAL_DEFAULTBIN";
        }
        /* for back-compatibility, we report it as default bin */
        if (type & UCDB_CVGBIN) {
            return "DEFAULTBIN";
        }
    }

    switch(type)
    {
    case UCDB_CVGBIN:       return "CVGBIN";
    case UCDB_COVERBIN:     return "COVERBIN";
    case UCDB_ASSERTBIN:    return "ASSERTBIN";
    case UCDB_SCBIN:        return "SCBIN";
    case UCDB_ZINBIN:       return "ZINBIN";
    case UCDB_STMTBIN:      return "STMTBIN";
    case UCDB_BRANCHBIN:    return "BRANCHBIN";
    case UCDB_EXPRBIN:      return "EXPRBIN";
    case UCDB_CONDBIN:      return "CONDBIN";
    case UCDB_TOGGLEBIN:    return "TOGGLEBIN";
    case UCDB_PASSBIN:      return "PASSBIN";
    case UCDB_FSMBIN:       return "FSMBIN";
    case UCDB_USERBIN:      return "USERBIN";
    case UCDB_COUNT:        return "COUNT";
    case UCDB_FAILBIN:      return "FAILBIN";
    case UCDB_VACUOUSBIN:   return "VACUOUSBIN";
    case UCDB_DISABLEDBIN:  return "DISABLEDBIN";
    case UCDB_ATTEMPTBIN:   return "ATTEMPTBIN";
    case UCDB_ACTIVEBIN:    return "ACTIVEBIN";
    case UCDB_IGNOREBIN:    return "IGNOREBIN";
    case UCDB_ILLEGALBIN:   return "ILLEGALBIN";
    case UCDB_DEFAULTBIN:   return "DEFAULTBIN";
    default:                return "UNKNOWNBIN";
    }
}

/*
 *  Static function that uses indentation level.
 */
static void
ucdb_print_cover(
    ucdbT               db,
    ucdbScopeT          parent,
    int                 coverindex,
    FILE*               output,
    ucdbSelectFlagsT    flags,
    int                 level,
	ucdbCoverTypeT		cover_mask)
{
    char* name;
    ucdbCoverDataT data;
    ucdbSourceInfoT sourceinfo;
    ucdbFlagsT coverflags;
    int flag_printed = 0;

    ucdb_GetCoverData(db,parent,coverindex,&name,&data,&sourceinfo);

	/* Don't print if mask doesn't match, used with ucdb_PrintScope */
	if (! (data.type & cover_mask))
		return;

	/* Always print source info with statement bins, as they can't be
	   identified any other way; they have no name. */
	if (data.type == UCDB_STMTBIN)
		flags |= UCDB_SELECT_SOURCEINFO;

    /*
     *  Line 1:
     *  Cover: name BINTYPE count=%d
     */
    fprintf(output,"%sCover: %s %s count=",
                   indent(level),
                   name ? name : "<no name>",
                   ucdb_cover_type_2string(data.type));
    if (data.flags & UCDB_IS_32BIT) {
        fprintf(output,"%u",data.data.int32);
    } else if (data.flags & UCDB_IS_64BIT) {
        fprintf(output,LLUSTR,data.data.int64);
    } else if (data.flags & UCDB_IS_VECTOR) {
        /* Not sure this is the right way to do it: */
        int i;
		int bits = data.bitlen;
		int bytelen = (bits/8) + ((bits%8) ? 1: 0);
        for ( i=0; i<=bytelen; i++ ) {
            if (i) fprintf(output,",");
            fprintf(output,"%02xc",data.data.bytevector[i]);
        }
    } else {
        fprintf(output,"ERROR");
    }
    fprintf(output,"\n");

    /*
     *  Line 2:
     *  flags: flag1 | flag2 | etc.
     */
    fprintf(output,"%sflags: ",indent(level+1));
    for ( coverflags=0x80000000; coverflags>0; coverflags = coverflags>>1) {
        if ((coverflags & data.flags) && flag_printed)
            fprintf(output," | ");
        if (coverflags & data.flags)
            flag_printed = 1;
		if (data.type & (UCDB_ASSERTIONBINS | UCDB_COVERBIN)) {
			/* Check assertion and cover directive specif flags */
        	switch(coverflags & data.flags) {
        	case UCDB_IS_EOS_NOTE:  fprintf(output,"IS_EOS_NOTE"); break;
        	case UCDB_IS_TLW_ENABLED: fprintf(output,"IS_TLW_ENABLED"); break;
        	case UCDB_HAS_ACTION:   fprintf(output,"HAS_ACTION"); break;
        	default: break;
        	}
		}
		if (data.type & UCDB_BRANCHBIN) {
			/* Check branch specif flags */
        	switch(coverflags & data.flags) {
        	case UCDB_IS_BR_ELSE:   fprintf(output,"IS_BR_ELSE"); break;
        	default: break;
        	}
		}
		if (data.type & UCDB_FSMBIN) {
			/* Check fsm specif flags */
        	switch(coverflags & data.flags) {
        	case UCDB_IS_FSM_TRAN:  fprintf(output,"IS_FSM_TRAN"); break;
        	default: break;
        	}
		}
		/* Check common flags */
        switch(coverflags & data.flags) {
        case UCDB_HAS_LIMIT:    fprintf(output,"HAS_LIMIT"); break;
        case UCDB_ENABLED:      fprintf(output,"ENABLED"); break;
        case UCDB_LOG_ON:       fprintf(output,"LOG_ON"); break;
        case UCDB_EXCLUDE_FILE: fprintf(output,"EXCLUDE_FILE"); break;
        case UCDB_EXCLUDE_PRAGMA: fprintf(output,"EXCLUDE_PRAGMA"); break;
        case UCDB_HAS_WEIGHT:   fprintf(output,"HAS_WEIGHT"); break;
        case UCDB_HAS_GOAL:     fprintf(output,"HAS_GOAL"); break;
        case UCDB_IS_VECTOR:    fprintf(output,"IS_VECTOR"); break;
        case UCDB_IS_64BIT:     fprintf(output,"IS_64BIT"); break;
        case UCDB_IS_32BIT:     fprintf(output,"IS_32BIT"); break;
        default: break;
        }
    }
    fprintf(output,"\n");

    /*
     *  Line 3:
     *  goal=%d weight=%d limit=%d
     */
    if (data.flags & (UCDB_HAS_GOAL | UCDB_HAS_WEIGHT | UCDB_HAS_LIMIT)) {
        fprintf(output,indent(level+1));
        if (data.flags & UCDB_HAS_GOAL) {
            fprintf(output,"goal = %d ", data.goal);
        }
        if (data.flags & UCDB_HAS_WEIGHT) {
            fprintf(output,"weight = %d ", data.weight);
        }
        if (data.flags & UCDB_HAS_LIMIT) {
            fprintf(output,"limit = %d ", data.limit);
        }
        fprintf(output,"\n");
    }

    /*
     *  Line 4:
     *  file (filenum), line=%d, token=%d
     */
    if (flags & UCDB_SELECT_SOURCEINFO) {
        if (ucdb_IsValidFileHandle(db,&sourceinfo.filehandle)) {
            fprintf(output,"%s%s (%d) line=%d token=%d\n",
                    indent(level+1),
                    ucdb_GetFileName(db,&sourceinfo.filehandle),
                    ucdb_GetFileNum(db,&sourceinfo.filehandle),
                    sourceinfo.line,
                    sourceinfo.token);
        }
    }

    /*
     *  Line 5:
     *  attributes
     */
    ucdb_print_attributes(db,parent,coverindex,output,level+1);
}


/*
 *  ucdb_PrintCover
 *  Print a simple dump of coveritem contents to the given file descriptor
 */
void
ucdb_PrintCover(
    ucdbT               db,
    ucdbScopeT          parent,     /* parent scope of coveritem */
    int                 coverindex, /* index of coveritem in parent */
    FILE*               output,     /* stdout if NULL */
    ucdbSelectFlagsT    flags)      /* affects what can appear to output */
{
    ucdb_print_cover(db,parent,coverindex,output,flags,0, -1);
}


/*------------------------------------------------------------------------------
 *  PrintScope
 *----------------------------------------------------------------------------*/
/*
 *  Convert scope type to a string
 */
static char*
ucdb_scope_type_2string(ucdbScopeTypeT type)
{
    switch(type)
    {
	case UCDB_TOGGLE:		return "TOGGLE";
	case UCDB_BRANCH:		return "BRANCH";
	case UCDB_EXPR:			return "EXPR";
	case UCDB_COND:			return "COND";
	case UCDB_INSTANCE:		return "INSTANCE";
	case UCDB_PROCESS:		return "PROCESS";
	case UCDB_BLOCK:		return "BLOCK";
	case UCDB_FUNCTION:		return "FUNCTION";
	case UCDB_FORKJOIN:		return "FORKJOIN";
	case UCDB_GENERATE:		return "GENERATE";
	case UCDB_GENERIC:		return "GENERIC";
	case UCDB_CLASS:		return "CLASS";
	case UCDB_COVERGROUP:	return "COVERGROUP";
	case UCDB_COVERINSTANCE:return "COVERINSTANCE";
	case UCDB_COVERPOINT:	return "COVERPOINT";
	case UCDB_CROSS:		return "CROSS";
	case UCDB_COVER:		return "COVER";
	case UCDB_ASSERT:		return "ASSERT";
	case UCDB_PROGRAM:		return "PROGRAM";
	case UCDB_PACKAGE:		return "PACKAGE";
	case UCDB_TASK:			return "TASK";
	case UCDB_INTERFACE:	return "INTERFACE";
	case UCDB_FSM:			return "FSM";
	case UCDB_TESTPLAN:		return "TESTPLAN";
	case UCDB_DU_MODULE:	return "DU_MODULE";
	case UCDB_DU_ARCH:		return "DU_ARCH";
	case UCDB_DU_PACKAGE:	return "DU_PACKAGE";
	case UCDB_DU_PROGRAM:	return "DU_PROGRAM";
	case UCDB_DU_INTERFACE:	return "DU_INTERFACE";
	case UCDB_FSM_STATES:	return "FSM_STATES";
	case UCDB_FSM_TRANS:	return "FSM_TRANS";
	case UCDB_GROUP:		return "GROUP";
	default:				return "UNKNOWNSCOPE";
    }
}

/*
 *  Convert source type to a string
 */
static char*
ucdb_source_type_2string(ucdbSourceT type)
{
    switch(type)
    {
    case UCDB_VHDL:			return "VHDL";
    case UCDB_VLOG:			return "VLOG";
    case UCDB_SV:			return "SV";
    case UCDB_SYSTEMC:		return "SYSTEMC";
    case UCDB_PSL_VHDL:		return "PSL_VHDL";
    case UCDB_PSL_VLOG:		return "PSL_VLOG";
    case UCDB_PSL_SV:		return "PSL_SV";
    case UCDB_PSL_SYSTEMC:	return "PSL_SYSTEMC";
    case UCDB_E:			return "E";
    case UCDB_VERA:			return "VERA";
    case UCDB_NONE:			return "NONE";
    case UCDB_OTHER:		return "OTHER";
    case UCDB_SOURCE_ERROR:	return "SOURCE_ERROR";
	default:				return "UNKNOWNSOURCE";
	}
}


/*
 *  This is a static function to implement recursion and indentation; the
 *  indentation corresponds to numbers of levels deep in recursion.
 */
static void
ucdb_print_scope(
    ucdbT               db,
    ucdbScopeT          scope,
    FILE*               output,
    ucdbSelectFlagsT    flags,
    int                 recurse,
    int                 level,
	ucdbScopeTypeT		scope_mask,
	ucdbCoverTypeT		cover_mask)
{
	int weight = ucdb_GetScopeWeight(db,scope);
	ucdbFlagsT scopeflags, myflags;
	int flag_printed = 0;
	ucdbScopeTypeT scopetype = ucdb_GetScopeType(db,scope);

	if (scopetype & scope_mask) {
		/*
		 *	Line 1:
		 *	Scope: hierarchical path name
		 */
		fprintf(output,"%sScope: %s\n",indent(level),
								ucdb_GetScopeHierName(db,scope));

		/*
		 *	Line 2:
		 *	type=SCOPETYPE src=SOURCETYPE [weight=%d] flags: flags1 | flags2 | etc.
		 */
		fprintf(output,"%stype=%s src=%s ",indent(level),
				ucdb_scope_type_2string(scopetype),
				ucdb_source_type_2string(ucdb_GetScopeSourceType(db,scope)));

		/* Only print weight if >= 0 and not equal to 1 */
		if (weight>=0 && weight!=1) {
			fprintf(output,"weight=%d ", weight);
		}

		myflags = ucdb_GetScopeFlags(db,scope);
		myflags = myflags & (~UCDB_SCOPE_INTERNAL); /* get rid of internal flags */
		for ( scopeflags=0x80000000; scopeflags>0; scopeflags = scopeflags>>1) {
			if ((scopeflags & myflags) && flag_printed)
				fprintf(output," | ");
			if (scopeflags & myflags)
				flag_printed = 1;
			switch(scopeflags & myflags) {
			case UCDB_INST_ONCE:		fprintf(output,"INST_ONCE"); break;
			case UCDB_ENABLED_STMT:		fprintf(output,"ENABLED_STMT"); break;
			case UCDB_ENABLED_BRANCH:	fprintf(output,"ENABLED_BRANCH"); break;
			case UCDB_ENABLED_COND:		fprintf(output,"ENABLED_COND"); break;
			case UCDB_ENABLED_EXPR:		fprintf(output,"ENABLED_EXPR"); break;
			case UCDB_ENABLED_FSM:		fprintf(output,"ENABLED_FSM"); break;
			case UCDB_ENABLED_TOGGLE:	fprintf(output,"ENABLED_TOGGLE"); break;
			case UCDB_ENABLED_TOGGLEEXT:fprintf(output,"ENABLED_TOGGLEEXT"); break;
			default: break;
			}
		}
		fprintf(output,"\n");

		/*
		 *	Line 3:
		 *  file (filenum), line=%d, token=%d
		 */
		if (flags & UCDB_SELECT_SOURCEINFO) {
			ucdbSourceInfoT sourceinfo;
			ucdb_GetScopeSourceInfo(db,scope,&sourceinfo);
			if (ucdb_IsValidFileHandle(db,&sourceinfo.filehandle)) {
				fprintf(output,"%s%s (%d) line=%d token=%d\n",
						indent(level),
						ucdb_GetFileName(db,&sourceinfo.filehandle),
						ucdb_GetFileNum(db,&sourceinfo.filehandle),
						sourceinfo.line,
						sourceinfo.token);
			}
		}

		/*
		 *	Line 4:
		 *	du='%s' if type==UCDB_INSTANCE
		 *	crossed coverpoints: <list> if type==UCDB_CROSS
		 */
		if (scopetype == UCDB_INSTANCE) {
			fprintf(output,"%sdu='%s'\n",indent(level),	
					ucdb_GetInstanceDUName(db,scope));
		} else if (scopetype == UCDB_CROSS) {
			int numcvps, cvp;
			fprintf(output,"%scrossed coverpoints: ",indent(level));
			ucdb_GetNumCrossedCvps(db,scope,&numcvps);
			for ( cvp=0; cvp<numcvps; cvp++ ) {
				fprintf(output,"%s ",ucdb_GetIthCrossedCvpName(db,scope,cvp));
			}
			fprintf(output,"\n");
		}

		/*
		 *  Line 5:
		 *  attributes
		 */
		ucdb_print_attributes(db,scope,-1,output,level);

	} /* end if scope type & scope mask */

	/*
	 *	Recurse, output 1 level indented
	 */
    if (recurse) {
        ucdbScopeT child = NULL;
        int num_covers = ucdb_GetScopeNumCovers(db,scope);
        int i;
        level = level+1;
        for ( i=0; i<num_covers; i++ ) {
            ucdb_print_cover(db,scope,i,output,flags,level,cover_mask);
        }
        while ((child = ucdb_NextSubScope(db,scope,child,-1))) {
            ucdb_print_scope(db,child,output,flags,1,level,
							 scope_mask,cover_mask);
        }
    }
}

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
    int                 recurse,	/* descend to child scopes */
	ucdbScopeTypeT		scope_mask,
	ucdbCoverTypeT		cover_mask)
{
    ucdb_print_scope(db,scope,output,flags,recurse,0,scope_mask,cover_mask);
}

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
    FILE*           output)         /* stdout if NULL */
{
	fprintf(output,"ucdb_PrintAttr: not implemented\n");
}

/*
 *  ucdb_PrintTestData
 *  Print a simple dump of a test data record to the given file descriptor.
 */
void
ucdb_PrintTestData(
    ucdbT               db,
    ucdbTestT           testdata,   /* test data record handle */
    FILE*               output,     /* stdout if NULL */
    ucdbSelectFlagsT    flags)      /* select attributes, tags etc. */
{
	fprintf(output,"ucdb_PrintTestData: not implemented\n");
}
