/******************************************************************************
 *	csv2ucdb: no-bells-and-whistles converter from tab-separated spreadsheet
 *	output to UCDB testplan file with implicit tagging.
 *
 *	This is also a very natural UCDB API Write Streaming Mode application:
 *	since CSV input is streaming, it makes a lot of sense to create the output
 *	as a stream.
 *
 *	See -help output for usage.
 *
 *****************************************************************************/
#include "ucdb.h"
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <assert.h>
#include <string.h>

#ifdef WIN32
#include <windows.h>
#include <time.h>
#define statTime double
#define CPU_TIME(stats) ((stats).cpuClock)
#else
#include <sys/time.h>
#include <sys/resource.h>
#define CPU_TIME(stats) \
    ((double)(stats).cpuClock.sec \
        + (((double)(stats).cpuClock.usec)/1000000) \
        + (double)(stats).sysClock.sec \
        + (((double)(stats).sysClock.usec)/1000000))
typedef struct {
	long sec;
    long usec;
}  statTime;
#endif

typedef struct {
    statTime cpuClock;
	statTime sysClock;
} historyStats;

/*
 *	Generic error handler.
 */
void error_handler(void		  *data,
				   ucdbErrorT *errorInfo)
{
	data = data;	/* ignored */
	fprintf(stderr,"UCDB error: %s\n", errorInfo->msgstr);
	if (errorInfo->severity == UCDB_MSG_ERROR)
		exit(1);
}


/*-----------------------------------------------------------------------------
 *	Forward declarations and constants
 *---------------------------------------------------------------------------*/
/* Extensions for output files (including '.'): */
const char* ucdb_ext = ".ucdb";
const char* do_ext = ".do";

void convert(char*);
void process_line(char*,ucdbT,int*,char*);

#define TRUE 1
#define FALSE 0
#define BOOLEAN int
#define TAGNAME "-tagname"


/*-----------------------------------------------------------------------------
 *	help()
 *---------------------------------------------------------------------------*/
void
help() {
	printf("\n");
    printf("Usage: csv2ucdb <file>.csv\n");
    printf("  Output in <file>.ucdb; \"csv\" can be any extension.\n");
    printf("\n");
    printf("Convert comma- or tab-separated spreadsheet text file for test plan to:\n");
    printf("* UCDB file with testplan hierarchy: <file>.ucdb\n");
    printf("  UCDB file has implicit tagging commands imbedded that automatically\n");
    printf("  associate testplan and coverage during the merge.\n");
	printf("\n");
    printf("  <file>.ext contains lines like the following:\n");
    printf("    \"1.1\",\"Title\",\"-cvgmatch cvg1; -cvgmatch cvg2\"\n");
	printf("\n");
    printf("  Note that the field separator does not matter, but all fields must be\n");
    printf("  double-quoted strings.\n");
    printf("  The third field must contain valid arguments to the 'coverage tag'\n");
    printf("  such as could be executed in vsim -viewcov loading the merged result.\n");
    printf("  Multiple sets of arguments must be separated by ';'\n");
}


/*-----------------------------------------------------------------------------
 *	main()
 *---------------------------------------------------------------------------*/
int
main(int argc, char* argv[])
{
	if (argc==1 || argc>2 || (argc==2 && strcmp(argv[1],"-help")==0)) {
		help();
	} else if (argc==2) {
		convert(argv[1]);
	}
	return 0;
}

/*-----------------------------------------------------------------------------
 *	Support for testplan history node creation
 *---------------------------------------------------------------------------*/

static void 
statSnapshot(historyStats* statData)
{
#ifdef WIN32
	OSVERSIONINFO osver;
	FILETIME c,e,KernelTime, UserTime;

	osver.dwOSVersionInfoSize = sizeof( osver ) ;
    if ( !GetVersionEx( &osver ) ) return;
    if ( osver.dwPlatformId != VER_PLATFORM_WIN32_NT ) return;

	if (GetProcessTimes(GetCurrentProcess(), &c, &e, &KernelTime, &UserTime)) {
      LARGE_INTEGER Kernel;
      LARGE_INTEGER User;

      Kernel.LowPart  = KernelTime.dwLowDateTime;
      Kernel.HighPart = KernelTime.dwHighDateTime;
      User.LowPart    = UserTime.dwLowDateTime;
      User.HighPart   = UserTime.dwHighDateTime;
	  statData->cpuClock = (double) (Kernel.QuadPart + User.QuadPart);
	} else {
	    statData->cpuClock = 0;
	}
#else
	struct rusage r_usage;
	
	if ( 0 == getrusage( RUSAGE_SELF, &r_usage)) {
		statData->cpuClock.sec = r_usage.ru_utime.tv_sec;
		statData->cpuClock.usec = r_usage.ru_utime.tv_usec;
		statData->sysClock.sec = r_usage.ru_stime.tv_sec;
		statData->sysClock.usec = r_usage.ru_stime.tv_usec;
	} else {
		statData->cpuClock.sec = 0;
		statData->cpuClock.usec = 0;
		statData->sysClock.sec = 0;
		statData->sysClock.usec = 0;
	}
#endif
}

static void 
statDiff(historyStats* statResult, historyStats* statFirst, historyStats* statLast)
{
#ifdef WIN32
    statResult->cpuClock = statLast->cpuClock - statFirst->cpuClock;
	statResult->cpuClock = (double)(statResult->cpuClock * CLOCKS_PER_SEC / 10000000);
	statResult->cpuClock = (double)statResult->cpuClock/1000;
#else
	statResult->cpuClock.sec = statLast->cpuClock.sec -
			                      statFirst->cpuClock.sec;
	statResult->cpuClock.usec = statLast->cpuClock.usec -
			                       statFirst->cpuClock.usec;
	statResult->sysClock.sec = statLast->sysClock.sec -
			                      statFirst->sysClock.sec;
	statResult->sysClock.usec = statLast->sysClock.usec -
			                       statFirst->sysClock.usec;
#endif
}

/*
 * createmergehistorynode
 *
 * Create the history node
 * Populate this file with the
 * appropriate testplan information.
 */
static void
createmergehistorynode(
    ucdbT db,
    char* ucdbpath,
	char* filepath,
	char* path,
	historyStats* statResult)
{
    ucdbHistoryNodeT testplanhistorynode;
    ucdbAttrValueT   attrvalue;
	char* cmdline;
	char* signature;
	char* prefix = "csv2ucdb ";
	int len;

    testplanhistorynode = 
		ucdb_CreateHistoryNode(db, ucdbpath, UCDB_HISTORYNODE_TESTPLAN);

    len = (strlen(prefix) + strlen(filepath) + 1);
	cmdline = malloc(len);
    sprintf(cmdline,"%s%s",prefix,filepath);
	attrvalue.type = UCDB_ATTR_STRING;
	attrvalue.u.svalue = cmdline;
	ucdb_AttrAdd(db, testplanhistorynode, -1, UCDBKEY_CMDLINE, &attrvalue);

	attrvalue.u.svalue = filepath;
	ucdb_AttrAdd(db, testplanhistorynode, -1, UCDBKEY_XMLSOURCE, &attrvalue);

    if ((path != NULL) && (path[0] != 0)) {
	    attrvalue.u.svalue = path;
	    ucdb_AttrAdd(db, testplanhistorynode, -1, UCDBKEY_PATH, &attrvalue);
	}

    signature = ucdb_CalculateHistorySignature(db,filepath);
    if ((signature != NULL) && (signature[0] != 0)) {
	    attrvalue.u.svalue = signature;
	    ucdb_AttrAdd(db, testplanhistorynode, -1, UCDBKEY_SIGNATURE, &attrvalue);
	}

	attrvalue.type = UCDB_ATTR_DOUBLE;
	attrvalue.u.dvalue = CPU_TIME(*statResult);
	ucdb_AttrAdd(db, testplanhistorynode, -1, UCDBKEY_CPUTIME, &attrvalue);
}

/*-----------------------------------------------------------------------------
 *	convert()
 *---------------------------------------------------------------------------*/
void
convert(char* filename)
{
	FILE* input = fopen(filename,"r");
	char* ucdbfilename = NULL;
	int i, len, bufsize, curline, c;
	char* line_buffer = NULL;
	char* filepath;
	ucdbT db;
    historyStats statStart;
    historyStats statStop;
    historyStats statResult;
	int prev_level = 0;
	char* tagcmd_buffer = NULL;
	int semicolons, max_semicolons;
	int tagcmd_bufsize = 0;

	if (input==NULL) {
		fprintf(stderr,"Unable to open %s: %s\n",filename,strerror(errno));
		exit(1);
	}

    statSnapshot(&statStart);

	/*
	 *	Recreate the commandline.
	 */
	len = strlen(filename) + 1;
	filepath = malloc(len);
	strcpy(filepath,filename);

	/* Find filename extension, if any, create output file names */
	i = strlen(filename)-1;
	while (i>=0 && filename[i]!='.')
		i--;
	if (i>=0)
		filename[i] = '\0';
	len = strlen(filename);

	/*
	 *	Create output UCDB file name, start write streaming mode
	 */
	ucdbfilename = malloc(len+strlen(ucdb_ext)+1);
	strcpy(ucdbfilename,filename);
	strcat(ucdbfilename,ucdb_ext);

    ucdb_RegisterErrorHandler(error_handler, NULL);
    db = ucdb_OpenWriteStream(ucdbfilename);
	assert(db);	/* NULL should be handled in error_handler */

	/* Scan input for maximum line size */
	max_semicolons = semicolons = curline = bufsize = 0;
	while ((c = getc(input)) != EOF) {
		if (c=='\n') {
			curline = 0;
			semicolons = 0;
		} else {
			if (c==';') {
				semicolons++;
				if (semicolons>max_semicolons)
					max_semicolons = semicolons;
			}
			curline++;
			if (curline>bufsize)
				bufsize=curline;
		}
	}
	bufsize = bufsize+2;	/* extra for '\n' and '\0' */
	line_buffer = malloc(bufsize);

	/*
	 *	Set up buffer for tag commands.
	 *
	 *	This is a somewhat ugly trick, but sets a probably much-too-big upper
	 *	bound for the TAGCMD attribute sizes.  Consider that we have to take
	 *	the third field (tag command arguments from csv) and add -tagname
	 *	"SECTION" (contents of the first field, the section number) to each
	 *	semicolon-separated command.
	 *
	 *	Upper bound for the TAGCMD (3rd field) is bufsize
	 *	Upper bound for the SECTION (1st field) is bufsize
	 *
	 *	Therefore, upper bound for TAGCMD attribute is:
	 *		bufsize + strlen(" -tagname \"SECTION\") * (max_semicolons+1)
	 *		= bufsize + (strlen("-tagname") + 4 + bufsize) * (max_semicolons+1)
	 */
	tagcmd_bufsize = bufsize + ((strlen(TAGNAME)+4+bufsize)
								* (max_semicolons+1));
	tagcmd_buffer = malloc(tagcmd_bufsize);

	if (line_buffer==NULL || tagcmd_buffer==NULL) {
		fprintf(stderr,"Memory allocation error\n");
		exit(1);
	}

	if (fseek(input,0,SEEK_SET)!=0) {
		fprintf(stderr,"Error processing input: %s\n",strerror(errno));
		exit(1);
	}

	/* Create top-level test plan node equal to the file base name */
	ucdb_CreateScope(db,NULL,
					 filename,		/* just the basename now */
					 NULL,			/* no source info */
					 1,				/* weight */
					 UCDB_OTHER,	/* source type */
					 UCDB_TESTPLAN,	/* scope type */
					 0);
	ucdb_WriteStream(db);

	while (fgets(line_buffer,bufsize,input)) {
		process_line(line_buffer,db,&prev_level,tagcmd_buffer);
	}

	/* finish writing scopes, including top-level */
	for ( i=0; i<=prev_level; i++ )
		ucdb_WriteStreamScope(db);

    statSnapshot(&statStop);
    statDiff(&statResult, &statStart, &statStop);
    createmergehistorynode(db,ucdbfilename,filepath,NULL,&statResult);

	ucdb_Close(db);				/* errors handled in error_handler */
	fclose(input);
	printf("UCDB file output in %s.\n", ucdbfilename);
	free(line_buffer);
	free(ucdbfilename);
}


/*-----------------------------------------------------------------------------
 *	process_line()
 *---------------------------------------------------------------------------*/
/* The add* functions insert '-tagname "SECTION"' before ';' and '\0' */
static void
add_string(
	char** tagcmd_buffer,
	char* string)
{
	while (*string) {
		*(*tagcmd_buffer)++ = *string++;
	}
}


static void
add_tagname(
	char** tagcmd_buffer,
	char* section)
{
	add_string(tagcmd_buffer," ");
	add_string(tagcmd_buffer,TAGNAME);
	add_string(tagcmd_buffer," \"");
	add_string(tagcmd_buffer,section);
	add_string(tagcmd_buffer,"\"");
}

static void
add_tagnames(
	char* tagcmd_buffer,
	char* section,
	char* tagargs)
{
	BOOLEAN quoted = FALSE;
	while (*tagargs) {
		if (*tagargs=='\"') {
			quoted = !quoted;
		}
		if (*tagargs == ';' && !quoted) {
			add_tagname(&tagcmd_buffer,section);
		}
		*tagcmd_buffer++ = *tagargs++;
	}
	add_tagname(&tagcmd_buffer,section);
	*tagcmd_buffer = '\0';
}


typedef enum {
	SECTION,
	TITLE,
	TAGCMD,
	NONE,
	DONE
} recordtypeT;

typedef enum {
	INIT,
	START,
	END
} recordT;

void
process_line(char* line, ucdbT db, int* prev_level, char* buffer)
{
	char* scan = line;
	char* start_of_record = NULL;
	char* section = NULL;
	char* title = NULL;
	char* tagargs = NULL;
	BOOLEAN in_string = FALSE;
	BOOLEAN escaped;
	recordT record = INIT;
	recordtypeT recordtype = NONE;
	int level;
	ucdbScopeT scope;
	ucdbAttrValueT attr;
	char* buffer_strduped = NULL;

	attr.type = UCDB_ATTR_STRING;

	/*
	 *	This is a state machine scanner to scan 3 record strings,
	 *	where the records are double-quoted.
	 *	Escaped quotes \" can be used inside quotes, \\ for a single backslash.
	 */
	while (*scan) {

		/*
		 *	Check for escape backslash, remove from input, set flag
		 */
		escaped = FALSE;
		if (*scan=='\\' && in_string) {
			/*
			 *	Moving characters in place ... a bad algorithm if there are
			 *	very big strings with lots of backslashes -- but saves having
			 *	to allocate a buffer to copy into.
			 */
			char* cur = scan;
			char* next = scan+1;
			while (*cur) {
				*(cur++) = *(next++);
			}
			escaped = TRUE;
		}

		switch(*scan) {
		case '"':
			if (!escaped) {
				in_string = !in_string;
				if (in_string) {
					switch(recordtype) {
					case NONE:		recordtype = SECTION;	break;
					case SECTION:	recordtype = TITLE;		break;
					case TITLE:		recordtype = TAGCMD;	break;
					case TAGCMD:	recordtype = DONE;
									record = INIT;		break;
					default: break;
					}
					start_of_record = scan+1;
				} else {
					*scan = '\0';
					if (recordtype==TAGCMD && record==START) {
						recordtype = DONE;
						record = END;
					}
				}
				break; /* for !escaped case */
			}
			/* fall through for escaped case */

		default:
			if (recordtype==TAGCMD && record==INIT) {
				record = START;
				tagargs = scan;
			}
			break;

		} /* end switch(*scan) */

		switch(recordtype) {
		case SECTION:
			if (in_string==FALSE && section==NULL) {
				int i;
				section = start_of_record;
				/*
				 *	calculate level of node by counting '.' in the section
				 *	number; e.g., "1.1" is level 2, "1.1.1" is level 3, etc.
				 */
				for ( level=1, i=0; section[i]; i++ ) {
					if (section[i]=='.')
						level++;
				}
			}
			break; /* end SECTION */

		case TITLE:
			if (in_string==FALSE && title==NULL) {
				title = start_of_record;
				sprintf(buffer,"%s",title);
				if (level <= *prev_level) {
					/*
					 *	This is an ancestor or sibling of the previously
					 *	created scope, need to call WriteStreamScope to
					 *	terminate the previous scope and maybe some of its
					 *	parents; consider what happens when "2" follows
					 *	"1.1.1".
					 */
					int i;
					for ( i=level; i<=(*prev_level); i++ )
						ucdb_WriteStreamScope(db);
				} else {
					/* We assume a child, not a grandchild */
					if (level > (*prev_level)+1) {
						fprintf(stderr,"Error with section '%s':\n",section);
						fprintf(stderr,"It is more than 1 level deeper than previous section.\n");
						exit(1);
					}
				}

				/* Create this scope */
				/*
				 *	Important note: need to copy buffer as string is not copied
				 *	by ucdb_CreateScope().
				 */
#if 0
				buffer_strduped = strdup(buffer);
#else
				buffer_strduped = (char *) malloc((strlen(buffer) + 1) * sizeof(char));
				strcpy(buffer_strduped, buffer);
#endif
				scope = ucdb_CreateScope(db,NULL,
										 buffer_strduped,/* title */
										 NULL,			/* no source info */
								 		 1,				/* weight */
								 		 UCDB_OTHER,	/* source type */
								 		 UCDB_TESTPLAN,	/* scope type */
								 		 0);
				*prev_level = level;

				/* Create a tag equal to the section # */
				ucdb_AddScopeTag(db,scope,section);
				/* Also create a SECTION attribute equal to the section # */
				attr.u.svalue = section;
				ucdb_AttrAdd(db,scope,-1,UCDBKEY_SECTION,&attr);
			}
			break; /* end TITLE */

		case DONE:
			if (tagargs && record==END) {
				add_tagnames(buffer,section,tagargs);
				attr.u.svalue = buffer;
				ucdb_AttrAdd(db,scope,-1,UCDBKEY_TAGCMD,&attr);
				tagargs = NULL;
			}
			break;

		default:
			break;
		} /* end switch(recordtype) */

		scan++;
	} /* end while (*scan) */

	/* Finish writing scope and its attributes and tags */
	ucdb_WriteStream(db);
	if (buffer_strduped)
		free(buffer_strduped);

} /* end process_line */
