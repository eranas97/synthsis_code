#include <stdlib.h>
#include "svdpi.h"
#include"dpiheader.h"

// this is the user define struct type to wrap up
// all the relelvant C data required for creating
// the SV dynamic array.

typedef struct {
   int  count;
   int* data;
} cdata_t;

static cdata_t*
create_C_data()
{
    int i, count;
    cdata_t* cdata;

    count = 100;
    cdata = (cdata_t*) malloc(sizeof(cdata_t));
    cdata->count =  count;
    cdata->data  =  (int*) malloc(count * sizeof(int));

    // initialize cdata to some known values, i.e. array indices themselves
    for (i = 0; i < count; ++i) {
        cdata->data[i] = i;
    }
    return cdata;
}

static void
cleanup_C_data(
    cdata_t* cdata)
{
    // cleanup
    if (cdata) {
        free(cdata->data);
    }
    free(cdata);
}

void create_sv_dynarray()
{
    cdata_t* cdata;
    int i;

    // existing target data from complex algorithm on C side
    cdata = create_C_data();

    // allocate a new SV dynamic array with a new size.
    alloc_sv_dynarray(cdata->count + 3, (void*) cdata);
}

void fetch_sv_dynarray_data_from_C(void* cdata, const svOpenArrayHandle hout)
{
    cdata_t* s = (cdata_t*) cdata;

    int *out = (int *)svGetArrayPtr(hout);

    // transfer the existing C data to the new dynamic array

    memcpy(out, s->data, sizeof(int) * s->count);

    // assign some known values to the 3 new elements.
    out[s->count]   = s->data[15];
    out[s->count+1] = s->data[18];
    out[s->count+2] = s->data[20];

    cleanup_C_data(cdata);
}
