/******************************************************************************
* UCIS API Example
*
* Usage: formal example
*
*****************************************************************************/
#include <vector>
#include <stdlib.h>
#include <stdio.h>
#include "ucis.h"
using namespace std;
int main(int argc, char* argv[]) // Single argument is the UCISDB name
{
    /* Formal example part 1: Open UCIS DB in memory mode */
    ucisT db = NULL;
    if (argc == 2) {
        db = ucis_Open(argv[1]);
    }
    if (db == NULL) {
        fprintf(stderr,"Unable to open UCISDB, or none provided\n");
        exit(1);
    }
    /* Formal example part 2: identity the formal test runs */
    ucisHistoryNodeT test;
    vector<ucisHistoryNodeT>::iterator itest;
    ucisIteratorT iterator;
    vector<ucisHistoryNodeT> formalTests; /* put formal tests in here */
    iterator = ucis_HistoryIterate(db,NULL,UCIS_HISTORYNODE_TEST);
    while ((test = ucis_HistoryScan(db, iterator))) {
        ucisFormalToolInfoT* toolInfo=NULL;
        ucisFormalEnvT formalEnv=NULL;
        char *coverageContext=NULL;
        ucis_FormalTestGetInfo(db,test,
                               &toolInfo,&formalEnv,&coverageContext);
        printf("Test \"%s\"\n",
               ucis_GetStringProperty(db, test, -1, UCIS_STR_HIST_LOG_NAME));
        if (toolInfo && formalEnv) { formalTests.push_back(test); }
    }
    ucis_FreeIterator (db, iterator);
    /* Formal example part 3: get the formal status info for all assert scopes */
    ucisScopeT scope;
    iterator = ucis_ScopeIterate(db,NULL,UCIS_ASSERT);
    while ((scope = ucis_ScopeScan(db, iterator))) {
        printf("Visiting scope: %s\n", ucis_GetStringProperty(db,scope,-1,
                                                              UCIS_STR_SCOPE_NAME));
        ucisFormalStatusT formalStatus;
        for (itest=formalTests.begin(); itest<formalTests.end(); itest++) {
            int none = ucis_GetFormalStatus(db, *itest, scope, &formalStatus);
            if (none) { continue; }
            const char *status_str = "?";
            switch (formalStatus) {
            case UCIS_FORMAL_PROOF:
                status_str = "Proven";
                break;
            case UCIS_FORMAL_FAILURE:
                status_str = "Failed";
                break;
            case UCIS_FORMAL_NONE:
                status_str = "None";
                break;
            case UCIS_FORMAL_INCONCLUSIVE:
                status_str = "Inconclusive";
                break;
            case UCIS_FORMAL_VACUOUS:
                status_str = "Vacuous";
                break;
            case UCIS_FORMAL_ASSUMPTION:
                status_str = "Assumption";
                break;
            case UCIS_FORMAL_CONFLICT:
                status_str = "Conflict";
                break;
            } // end switch
            printf("Assertion %s in test %s is %s!\n",
                   ucis_GetStringProperty(db,scope,-1, UCIS_STR_SCOPE_NAME),
                   ucis_GetStringProperty(db, *itest, -1, UCIS_STR_TEST_NAME),
                   status_str);
        } // end for all formal tests
    } // end for all assert scopes
    ucis_FreeIterator (db, iterator);
    return(0);
}
