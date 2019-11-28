/*
//
// Copyright 2006-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// UCDB Crawler
//
// This is an interactive crawler of the UCDB in-memory data model.
//
// Usage: see help output:
//
//       ucdbcrawler -help
//       
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
#include <errno.h>

/* include UCDB API header */
#include "ucdb.h"

/* include ucdb print utilities header (in this directory) */
#include "ucdb_print.h"

#define RECORDING_FILENAME "ucdbcrawl.input"


/*----------------------------------------------------------------------------
 *   help()
 *---------------------------------------------------------------------------*/
void
help(FILE* outfile)
{
    fprintf(outfile,"Available commands:\n\
Commands are one letter sensitive, whole word may be given\n\
Arguments are whitespace sensitive, escaped ids OK in strings\n\
Previous input can be repeated with carriage return\n\
(NI means not implemented)\n\
q[uit]            : quit\n\
? | h[elp]        : help\n\
g[oto] <path>     : go to scope by path name in the database\n\
g[oto] -du <name> :NI: goto named design unit\n\
w[here]           : print current path in the database\n\
p[rint]           : print information about current object\n\
p[rint] -r        : recursive print from current object down\n\
p[rint] -s        : print names of subscopes only\n\
p[rint] -c        : print all child coveritems only\n\
p[rint] -a        :NI: print attributes for current object\n\
p[rint] -t        :NI: print all test data records in UCDB\n\
u[p]              : go to parent, if any\n\
d[own]            : go to first scope child, or first coveritem if none\n\
d[own] -c <num>   : go to nth coveritem child\n\
n[ext]            : go to sibling scope or coveritem\n\
r[ecord]          : record input in %s\n\
f[ilter]          : display current filter masks (refer to ucdb.h)\n\
f[ilter] <flags>  : filter recursive print according to type:\n\
  <flags> are any of: -cvg | -code bcestf | -dir | -assert | -all\n",
	RECORDING_FILENAME);
}


/*
 *  This one prints a "current object" whether it is a scope or coverindex
 */
void
print_scope_or_cover(ucdbT db,
                     FILE* outfile,
                     ucdbScopeT scope,
                     int coverindex,
                     int recursive,
                     ucdbScopeTypeT scope_mask,
                     ucdbCoverTypeT cover_mask)
{
    if (scope==NULL)
        fprintf(outfile,"At database root\n");
    else if (coverindex==(-1)) {
        ucdb_PrintScope(db,scope,outfile,(ucdbSelectFlagsT)(-1),recursive,
                        scope_mask,cover_mask);
    } else
        ucdb_PrintCover(db,scope,coverindex,outfile,(ucdbSelectFlagsT)(-1));
}

void
print_current_object(ucdbT db,
                     FILE* outfile,
                     ucdbScopeT scope,
                     int coverindex)
{
	print_scope_or_cover(db,outfile,scope,coverindex,0,-1,-1);
}

void
print_current_subtree(ucdbT db,
                      FILE* outfile,
                      ucdbScopeT scope,
                      ucdbScopeTypeT scope_mask,
                      ucdbCoverTypeT cover_mask)
{
	if (scope) {
		print_scope_or_cover(db,outfile,scope,-1,1,scope_mask,cover_mask);
	} else {
		ucdbScopeT toplevel_scope = NULL;
		while ((toplevel_scope = ucdb_NextSubScope(db,NULL,toplevel_scope,-1))) {
			print_scope_or_cover(db,outfile,toplevel_scope,-1,1,scope_mask,
								 cover_mask);
		}
	}
}

/*
 *  Print children scopes in a relatively simple fashion.
 *  If scope==NULL note that this dumps the top-level nodes.
 */
void
print_children_scopes(ucdbT db,
                      FILE* outfile,
                      ucdbScopeT scope)
{
    ucdbScopeT child = NULL;
    while ((child = ucdb_NextSubScope(db,scope,child,-1 /* all types */))) {
        ucdb_PrintScope(db,child,outfile,
                        0 /* select minimal info */,
                        0 /* not recursive */,
                        -1 /* scope type mask */,
                        -1 /* cover type mask */);
    }
}


/*
 *	Print children coveritems in a relatively simple fashion.
 *	In this case, scope cannot be NULL.
 */
void
print_children_covers(ucdbT db,
					  FILE* outfile,
					  ucdbScopeT scope)
{
	int coverindex, num_covers;
	if (scope==NULL)
		return;
	num_covers = ucdb_GetScopeNumCovers(db,scope);
	for ( coverindex=0; coverindex < num_covers; coverindex++ ) {
		ucdb_PrintCover(db,scope,coverindex,outfile,
						0 /* select minimal info */);
	}
}


/*
 *	Go from current object to first child scope.
 */
ucdbScopeT
goto_child_scope(ucdbT db,
				 ucdbScopeT current_scope,
				 int current_coverindex)
{
	if (current_coverindex>=0) {
		/* if the "current" object is a coveritem, there can be no child! */
		return NULL;
	}
	return ucdb_NextSubScope(db,current_scope,NULL,-1);
}


/*
 *	Go from current object to given child cover.
 */
int
goto_child_cover(ucdbT db,
				 ucdbScopeT scope,
				 int current_coverindex,
				 int goto_coverindex)
{
	if (current_coverindex>=0) {
		/* if the "current" object is a coveritem, there can be no child! */
		return -1;
	} else {
		/* Do a bounds check on the "goto" coverindex */
		int numcovers = ucdb_GetScopeNumCovers(db,scope);
		if (goto_coverindex<0 || goto_coverindex>=numcovers) {
			return -1;
		} else {
			return goto_coverindex;
		}
	}
}


/*----------------------------------------------------------------------------
 *  get_input()
 *  Simple function to return input string.  Returns static data so data must
 *  be copied if get_input() is re-used in the lifetime of the data.  Always
 *  returns a valid string, but string may be empty.  Only works on input lines
 *  up to INPUTLEN-1 in length.
 *  If given an empty string, will return copy of input buffer from previous
 *	input.
 *---------------------------------------------------------------------------*/
/* Note: It is always better to use a dynamic string type if available */
#define INPUTLEN 1024
typedef char inputBufferT[INPUTLEN];
static FILE* recording_file = NULL;

static char*
get_input(FILE* infile,
          int recording_on)
{
	static inputBufferT input = "";
	static inputBufferT prev_input = "";
    char* last_char;
    int last_index;

    if (fgets(input,sizeof(inputBufferT),infile)==NULL) {
		input[0] = '\0';
    } else {
        if (recording_on) {
            if (recording_file==NULL) {
                recording_file = fopen(RECORDING_FILENAME,"w");
                if (recording_file==NULL) {
                    fprintf(stderr,"Unable to open output '%s' -- %s\n",
                        RECORDING_FILENAME, strerror(errno));
                    exit(1);
                }
            }
            fprintf(recording_file,input);
        }

        /* Remove a terminating '\n' if read from input */
        last_index = strlen(input)-1;
        if (last_index>=0) {
            last_char = &input[last_index];
            if (*last_char == '\n')
                *last_char = '\0';
        }

		/* Save or use previous input */
		if (input[0] == '\0' && prev_input[0] != '\0') {
			strcpy(input,prev_input);
		} else if (input[0] != '\0') {
			strcpy(prev_input,input);
		}
    }
    return &input[0];
}

/*-----------------------------------------------------------------------------
 *  get_command_args
 *  This skips past the first word and first whitespace to return the remainder
 *  of a command string.  The only recognized whitespace character is the space
 *	(' ').
 *  Returns NULL if no arguments.
 *---------------------------------------------------------------------------*/
char*
get_command_args(char* command_input)
{
    char* args = command_input;
	
    while (*args && *args == ' ')
        args++;
    while (*args && *args != ' ')
        args++;
    while (*args && *args == ' ')
        args++;
    if (*args)
        return args;
    else
        return NULL;
}


/*-----------------------------------------------------------------------------
 *  arg_compare
 *  Compares args against substring given by second argument.  1 if equal.
 *---------------------------------------------------------------------------*/
int
arg_compare(const char* arg,
            const char* substring)
{
    if (arg==NULL)
        return 0;
    return ! strncmp(arg,substring,strlen(substring));
}


/*-----------------------------------------------------------------------------
 *  int64_to_hex_string
 *  Converts an input int64_t into a string in a platform-independent manner.
 *---------------------------------------------------------------------------*/
static char* int64_to_hex_string(int64_t val)
{
	static char buf[100];
    sprintf(buf, LLXSTR, val);
    return buf;
}


/*----------------------------------------------------------------------------
 *  command_loop
 *      - loop waiting for user input from command line
 *      - See help() function for available commands.
 *---------------------------------------------------------------------------*/
void
command_loop(ucdbT db,
             FILE* infile,
             FILE* outfile)
{
    char*           input = NULL;
    ucdbScopeT      current_scope = NULL;
    int             current_coverindex = -1;
    ucdbScopeTypeT  scope_mask = -1;
    ucdbCoverTypeT  cover_mask = -1;
    int             recording_on = 0;

    fprintf(outfile,"? for help:\n");
    while (1) {
        char* args = NULL;
        fprintf(outfile,"> ");
        input = get_input(infile,recording_on);
        switch(input[0]) {

        case '?': case 'h':
            /* help | ? */
            help(outfile);
            break;

        case 'q':
            /* quit */
            if (recording_file) {
                fprintf(outfile,"Recording done to file '%s'\n",
                                RECORDING_FILENAME);
                fclose(recording_file);
            }
            exit(0);
            break;

		case 'd':
			/* down */
			args = get_command_args(input);
			if (current_coverindex >= 0) {
				fprintf(outfile,"Current object is a coveritem; cannot go down\n");
				break;
			} else if (args==NULL) {
				ucdbScopeT child_scope = goto_child_scope(db,current_scope,
														  current_coverindex);
				if (child_scope==NULL) {
					if (ucdb_GetScopeNumCovers(db,current_scope)>0) {
						current_coverindex = 0;
					} else {
						fprintf(outfile,"Cannot go down\n");
						break;
					}
				} else {
					current_scope = child_scope;
					current_coverindex = -1;
				}
			} else if (arg_compare(args,"-c")) {
				int arg_coverindex;		/* from input */
				args = get_command_args(args);
				if (args) {
					if (sscanf(args,"%d",&arg_coverindex)!=1) {
						arg_coverindex = -1;
					}
				} else {
					/* No argument given will mean goto coveritem # 0 */
					arg_coverindex = 0;
				}
				if (arg_coverindex == -1) {
					fprintf(outfile,"Expecting cover index after -c\n");
					break;
				} else {
					int child_coverindex = goto_child_cover(db,current_scope,
															current_coverindex,
															arg_coverindex);
					if (child_coverindex>=0) {
						current_coverindex = child_coverindex;
					} else {
						fprintf(outfile,"Cannot go down to child cover %d\n",
								arg_coverindex);
						break;
					}
				}
			}
			print_current_object(db,outfile,current_scope,current_coverindex);
			break;

        case 'f':
            /* filter */
            args = get_command_args(input);
            if (args==NULL) {
                fprintf(outfile, "Scope type mask = %s, ", int64_to_hex_string(scope_mask));
                fprintf(outfile, "cover type mask = %s\n", int64_to_hex_string(cover_mask));
                break;
            } else {
                scope_mask = cover_mask = 0;
            }
            while (args) {
                if (arg_compare(args,"-cvg")) {
                    cover_mask |= UCDB_CVGBIN | UCDB_IGNOREBIN |
                        UCDB_ILLEGALBIN | UCDB_DEFAULTBIN;
                    scope_mask |= UCDB_COVERGROUP | UCDB_COVERINSTANCE |
                        UCDB_COVERPOINT | UCDB_CROSS;
				} else if (arg_compare(args,"-dir")) {
					cover_mask |= UCDB_COVERBIN | UCDB_FAILBIN;
					scope_mask |= UCDB_COVER;
				} else if (arg_compare(args,"-assert")) {
					cover_mask |= UCDB_ASSERTBIN | UCDB_VACUOUSBIN |
						UCDB_DISABLEDBIN | UCDB_ATTEMPTBIN | UCDB_ACTIVEBIN;
					scope_mask |= UCDB_ASSERT;
				} else if (arg_compare(args,"-code")) {
					char* argp = args = get_command_args(args);
					while (*argp && *argp != ' ') {
						switch(*args) {
						case 'b':
							cover_mask |= UCDB_BRANCHBIN;
							scope_mask |= UCDB_BRANCH;
							break;
						case 'c':
							cover_mask |= UCDB_CONDBIN;
							scope_mask |= UCDB_COND;
							break;
						case 'e':
							cover_mask |= UCDB_EXPRBIN;
							scope_mask |= UCDB_EXPR;
							break;
						case 's':
							cover_mask |= UCDB_STMTBIN;
							break;
						case 't':
							cover_mask |= UCDB_TOGGLEBIN;
							scope_mask |= UCDB_TOGGLE;
							break;
						case 'f':
							cover_mask |= UCDB_FSMBIN;
							scope_mask |= UCDB_FSM | UCDB_FSM_STATES | UCDB_FSM_TRANS;
							break;
						default:
							fprintf(outfile,"Unrecognized -code argument: '%c'\n",
									*argp);
						} /* end switch (*argp) */
						argp++;
					} /* end while (*args) */
                } else if (arg_compare(args,"-all")) {
                    cover_mask = scope_mask = -1;
                } else {
                    fprintf(outfile,"Unrecognized argument in '%s'\n",
                            args);
                }
                args = get_command_args(args);
            }
            break;

        case 'g':
            /* goto */
            args = get_command_args(input);
            if (args==NULL) {
                fprintf(outfile,"Argument expected to '%s'\n",input);
				break;
            }
            else if (strncmp(args,"-du ",strlen("-du "))==0) {
                /* get design unit by name */
            } else {
                /* get instance by name */
                ucdbScopeT goto_scope = ucdb_MatchScopeByPath(db,args);
				if (goto_scope) {
					current_scope = goto_scope;
					current_coverindex = -1;
				} else {
                    fprintf(outfile,"Scope not found: '%s'\n",args);
					break;
                }
            }
			print_current_object(db,outfile,current_scope,current_coverindex);
            break;

		case 'n':
			/* next */
			if (current_coverindex >= 0) {
				/* Increment current cover index, if a sibling exists */
				if (current_coverindex+1
					== ucdb_GetScopeNumCovers(db,current_scope)) {
					fprintf(outfile,"At end of children\n");
					break;
				}
				current_coverindex++;
			} else {
				/* Go to sibling scope, if exhausted try covers */
				ucdbScopeT parent_scope = ucdb_ScopeParent(db,current_scope);
				ucdbScopeT sibling_scope = ucdb_NextSubScope(db,parent_scope,
															 current_scope,-1);
				if (sibling_scope) {
					current_scope = sibling_scope;
				} else if (ucdb_GetScopeNumCovers(db,parent_scope)) {
					current_scope = parent_scope;
					current_coverindex = 0;
				} else {
					fprintf(outfile,"At end of children\n");
					break;
				}
			}
			print_current_object(db,outfile,current_scope,current_coverindex);
			break;

        case 'p':
            /* print */
            args = get_command_args(input);
            if (args==NULL) {
                print_current_object(db,outfile,
                                     current_scope,
                                     current_coverindex);
            } else if (strcmp(args,"-r")==0) {
				if (current_coverindex>=0) {
					fprintf(outfile,"Can't do recursive print of coveritem\n");
				} else {
	                print_current_subtree(db,outfile,
	                                      current_scope,
    	                                  scope_mask,cover_mask);
				}
            } else if (strcmp(args,"-s")==0) {
                print_children_scopes(db,outfile,
                                      current_scope);
            } else if (strcmp(args,"-c")==0) {
                print_children_covers(db,outfile,
                                      current_scope);
            } else {
                fprintf(outfile,"Unrecognized argument: '%s'\n",args);
            }
            break;

        case 'r':
            /* record */
            recording_on = 1;
            fprintf(outfile,"Recording ON\n");
            break ;

		case 'u':
			/* up */
			if (current_coverindex >=0) {
				/* "Moves" from coveritem to its parent */
				current_coverindex = -1;
			} else if (current_scope) {
				current_scope = ucdb_ScopeParent(db,current_scope);
			}
			print_current_object(db,outfile,current_scope,current_coverindex);
			break;

        case 'w':
            /* where */
            fprintf(outfile,"Current scope path: %s\n",
                    current_scope
                    ? ucdb_GetScopeHierName(db,current_scope)
                    : "(none)");
			if (current_coverindex >= 0) {
				fprintf(outfile,"Current coveritem index: %d\n",
						current_coverindex);
			}
            break ;

        default:
            fprintf(outfile,"Unrecognized command: '%s'\n", input);
            help(outfile);

        } /* end switch */
    } /* end while (1) */

} /* end command_loop() */


/*----------------------------------------------------------------------------
 *  error_handler
 *      - generic error handler
 *---------------------------------------------------------------------------*/
void
error_handler(void       *data,
              ucdbErrorT *errorInfo)
{
    assert(data == NULL);
    fprintf(stderr, "%s\n", errorInfo->msgstr);
}


/*----------------------------------------------------------------------------
 *  usage
 *---------------------------------------------------------------------------*/
void
usage(char* program_name,
      int exit_code)
{
    printf("Usage: %s <ucdb file> [-i <input file>] [-o <output file>]\n",
           program_name);
    printf("       UCDB file is required.\n");
    printf("       With no input file, this is interactive.  An input file\n");
    printf("       must use interactive syntax.  See interactive help.\n");
    printf("       For interactive help, run and use '?' at the prompt.\n");
    exit(exit_code);
}


/*-----------------------------------------------------------------------------
 *  main
 *---------------------------------------------------------------------------*/
int
main(int    argc, 
     char **argv)
{
    ucdbT db;
    FILE *input_file, *output_file;
    char* output_filename = NULL;
    char* input_filename = NULL;
    char* ucdb_filename = NULL;
    char* program_name = argv[0];
    int i;

    /* "Parse" command-line options.  Assign filenames, only once, otherwise
     * exit with usage message.
     */
    for ( i=1; i<argc; i++ ) {
        switch (*argv[i]) {
        case '-':
            if (strcmp(argv[i],"-i")==0) {
                if (input_filename)
                    usage(program_name,1);
                else
                    input_filename = argv[++i];
            } else if (strcmp(argv[i],"-o")==0) {
                if (output_filename)
                    usage(program_name,1);
                else
                    output_filename = argv[++i];
            } else if (strncmp(argv[i],"-help",strlen(argv[i]))==0) {
                usage(program_name,1);
            }
            break;
        default:
            if (ucdb_filename)
                usage(program_name,1);
            else
                ucdb_filename = argv[i];
            break;
        } /* end switch */
    } /* end for */

    if (ucdb_filename==NULL)
        usage(program_name,1);

    /*  If we got here, time to open all files */

    if (input_filename) {
        if ((input_file=fopen(input_filename,"r"))==NULL) {
            fprintf(stderr,"Unable to open input '%s' -- %s\n",
                    input_filename, strerror(errno));
        }
    } else
        input_file = stdin;

    if (output_filename) {
        if ((output_file=fopen(output_filename,"w"))==NULL) {
            fprintf(stderr,"Unable to open output '%s' -- %s\n",
                    output_filename, strerror(errno));
        }
    } else
        output_file = stdout;

    /* This is the UCDB open part; if successful, call command loop */

    ucdb_RegisterErrorHandler(error_handler, NULL);
    db = ucdb_Open(ucdb_filename);
    if (db) 
        command_loop(db,input_file,output_file);
    /* Error case will be handled by error_handler() */

    return 0;
}
