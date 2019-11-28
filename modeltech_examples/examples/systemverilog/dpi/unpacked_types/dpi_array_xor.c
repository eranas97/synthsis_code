
#define P1364_VECVAL
#include "svdpi.h"
#include "dpi_array_xor.h"
#include "vpi_user.h"


/*
 * This function demonstrates robustly implemented array processing code.
 * Preprocessor constants are used for easy readjustment of array bounds.
 */
#define NBITS 64
#define NWORDS 16
void xor_4st_6416(
    svLogicVecVal* out,
    const svLogicVecVal* in)
{
    int iunpacked, ipacked;

    /* Zero all control bits + data bits */
    for (ipacked = 0; ipacked < SV_PACKED_DATA_NELEMS(NBITS); ipacked++) {
        out[ipacked].bval = 0;
        out[ipacked].aval = 0;
    }

    for (iunpacked = 0; iunpacked < NWORDS; iunpacked++) {
        for (ipacked = 0; ipacked < SV_PACKED_DATA_NELEMS(NBITS); ipacked++) {
            out[ipacked].aval ^= in[2*iunpacked+ipacked].aval;
        }
    }
}


/*
 * This function demonstrates quick-n-dirty array processing code
 * that is actually easier to read, but less maintainable.
 */
void xor_2st_6416(
    svBitVecVal* out,
    const svBitVecVal* in)
{
    int i;

    /* Initialize output data bits to zero */
    out[0] = 0;
    out[1] = 0;

    for (i = 0; i < 16; i++) {
        out[0] ^= in[2*i];
        out[1] ^= in[2*i+1];
    }
}


/*
 *  The same basic idea.  No typedef in the SystemVerilog code.
 */
void xor_2st_6416a(
    svBitVecVal* out,
    const svBitVecVal* in)
{
    int iunpacked, ipacked;

    /* Initialize output data bits to zero */
    for (ipacked = 0; ipacked < 2; ipacked++) {
        out[ipacked] = 0;
    }

    for (iunpacked = 0; iunpacked < 16; iunpacked++) {
        for (ipacked = 0; ipacked < 2; ipacked++) {
            out[ipacked] ^= in[2*iunpacked+ipacked];
        }
    }
}



/*
 * 64-bit 2-state vector version
 */
void xor_longint16(
    uint64_t* out,
    const uint64_t* in)
{
    int i;
    for (i = 0; i < NWORDS; i++) {
        *out ^= in[i];
    }
}
