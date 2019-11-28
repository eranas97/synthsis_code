/******************************************************************************
* UCIS API Example
*
* Usage: dump_UIDs <ucisdb name> [-p <pathsep char>] [-o <output filename>]
*
* Generate a list of all the UIDs (scopes and coveritems) in the UCISDB
*
*****************************************************************************/
#include "ucis.h"
#include <stdio.h>
#include <stdlib.h>

static char ps = '/'; /* default path separator */

void error_handler(void *cr_data,
                   ucisErrorT *errorInfo)
{
    fprintf(stderr, "UCIS error: %s\n", errorInfo->msgstr);

    if (errorInfo->severity == UCIS_MSG_ERROR) {
        exit(1);
    }
}

/*---------------------------------------------------------------------------
*   cr_read_cb
*        - callback function for read streaming mode.
*---------------------------------------------------------------------------*/
ucisCBReturnT cr_read_cb(void          *userData,
                         ucisCBDataT  *cbData)
{
    ucisT db  = cbData->db;
    void* obj = cbData->obj;
    int coverindex = cbData->coverindex;

    FILE* outFile = (FILE*) userData;

    switch (cbData->reason)
    {
    case UCIS_REASON_CVBIN:
    case UCIS_REASON_DU:
    case UCIS_REASON_SCOPE:
        fprintf(outFile,
                ucis_GetStringProperty(db,obj,coverindex,UCIS_STR_UNIQUE_ID));
        fprintf(outFile, "\n");
        break;
    case UCIS_REASON_INITDB:
        ucis_SetPathSeparator(db, ps);
        break;
    default:
        break;
    }
    return UCIS_SCAN_CONTINUE;
}

/*---------------------------------------------------------------------------
*    main
*       - process arguments
*       - register error handler
*       - open database in read streaming mode with callback
*---------------------------------------------------------------------------*/
int main(int    argc,
         char **argv)
{
    char* outFileName   = NULL;
    char* inputFileName = NULL;
    FILE* outFile       = NULL;
    int   i;
    /*---------------------------------------------------------------------
     * argument processing phase
     *---------------------------------------------------------------------*/

    for (i = 1; i < argc; i++)
    {
        switch (*argv[i])
        {
        case '-':
            switch (*(argv[i] + 1)) {
            case 'o':
                outFileName = argv[++i];
                outFile = fopen(outFileName,"w");
                if (outFile == NULL) {
                    fprintf(stderr, "Error opening %s\n", outFileName);
                    exit(1);
                }
                break;
            case 'p':
                i++;
                ps = *argv[i];
                fprintf(stderr, "Path separator used in UID will be %c\n", ps);
                break;
            default:
                fprintf(stderr, "Illegal option name %s\n", argv[i]);
                break;
            }
            break;
        default:
            inputFileName = argv[i];
            break;
        }
    }
    
    if (inputFileName == NULL) {
        fprintf(stderr,"Usage: dump_UIDs <ucisdb name> [-o <outfile>] [-p <pathsep char>]]\n");
        exit(1);
    }
    
    if (outFile == NULL) {
        outFile = stdout;
    }
    
    /*---------------------------------------------------------------------
     * setup phase
     *---------------------------------------------------------------------*/

    ucis_RegisterErrorHandler(error_handler, NULL);

    /*---------------------------------------------------------------------
     * data collection phase
     *---------------------------------------------------------------------*/

    ucis_OpenReadStream(inputFileName, cr_read_cb, outFile);
        
    /*---------------------------------------------------------------------
     * cleanup phase
     *---------------------------------------------------------------------*/
    
    if (outFile != stdout) {
        fclose(outFile);
    }
    
    return 0;
}
