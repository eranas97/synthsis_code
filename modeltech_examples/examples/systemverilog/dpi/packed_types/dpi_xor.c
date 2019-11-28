
#define P1364_VECVAL
#include "dpi_xor.h"
#include "vpi_user.h"


/*
 * 64-bit unsigned int version
 */
void xor_longint(
    uint64_t *z,
    uint64_t i0,
    uint64_t i1)
{
    *z = i0 ^ i1;
}


/*
 * 64-bit 4-state vector version
 * To do accurate work with 4-state data, we need to
 * detect any X or Z bits in the input arguments and
 * write X values into the corresponding bits of the output.
 */
void xor_logicvec64(
    svLogicVecVal* z,
    const svLogicVecVal* i0,
    const svLogicVecVal* i1)
{
    int n;
    for (n = 0; n < SV_PACKED_DATA_NELEMS(64); n++) {
        z[n].aval  = i0[n].aval ^ i1[n].aval;  /* XOR data bits */
        z[n].bval  = i0[n].bval | i1[n].bval;  /* Union of all control bits */
        z[n].aval |= z[n].bval;                /* Turn all Z and X to X (a=1,b=1)*/
    }
}


/*
 * 64-bit 2-state vector version
 */
void xor_bitvec64(
    svBitVecVal* z,
    const svBitVecVal* i0,
    const svBitVecVal* i1)
{
    int n;
    for (n = 0; n < SV_PACKED_DATA_NELEMS(64); n++) {
        z[n] = i0[n] ^ i1[n];
    }
}
