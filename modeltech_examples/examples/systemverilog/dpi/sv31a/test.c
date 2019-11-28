/*
 * DPI C functions for SV3.1a example.
 */

#include "vpi_user.h"
#include "dpiheader.h"
#include "svdpi.h"

/*
 * The original SV3.1a-compliant user routines are named with suffix string "_sv31a".
 * The routines are not compliant with IEEE-1800 and the code needs to be ported.
 *
 * The goal of this example is to show how to reuse these existing SV3.1a C routines 
 * with a minimum of effort if one wants to convert SV3.1a "DPI" to P1800 "DPI-C".
 */ 
static int64_t c_bitvec_sv31a(const svBitPackedArrRef iv, svBitPackedArrRef ov)
{
    svBitVec32  canon_val[SV_CANONICAL_SIZE(64)];
    svBitVec32  partsel = 0;

    /* assign the input vector to intermediate value 'canon_val', which is in 3.1a canonical format.*/
    svGetBitVec32(canon_val, iv, 64);

    /* assign the intermediate value (in canonical format) to the output vector.*/
    svPutBitVec32(ov, canon_val, 64);

    /* get the highest 4 bits of the input vector (bit [60:63]).*/
    svGetPartSelectBit(&partsel, iv, 60, 4);

    /* copy to the lowest 4 bits of the output vector (bit [3:0]).*/
    svPutPartSelectBit(ov, partsel, 0, 4);

    /* overwrite the bit at offset 5 to value 1'b1.*/
    svPutSelectBit(ov, 5, sv_1);

    /* return 64-bit from offset 0.*/
    return (int64_t) svGet64Bits(ov, 0);
}

static svLogic c_logicvec_sv31a(const svLogicPackedArrRef iv, svLogicPackedArrRef ov)
{
    svLogicVec32  canon_val[SV_CANONICAL_SIZE(64)];
    svLogicVec32  partsel = { 0 };

    /* assign the input vector to intermediate value 'canon_val', which is in 3.1a canonical format.*/
    svGetLogicVec32(canon_val, iv, 64);

    /* assign the intermediate value (in canonical format) to the output vector.*/
    svPutLogicVec32(ov, canon_val, 64);

    /* get the highest 4 bits of the input vector (logic [60:63]).*/
    svGetPartSelectLogic(&partsel, iv, 60, 4);

    /* copy to the lowest 4 bits of the output vector (logic [3:0]).*/
    svPutPartSelectLogic(ov, partsel, 0, 4);

    /* overwrite the bit at offset 5 to value 1'b1.*/
    svPutSelectLogic(ov, 5, sv_1);

    /* return lowest bit of output.*/
    return svGetSelectLogic(ov, 0);
}


int64_t
c_bitvec(
    const svBitVecVal* iv,
    svBitVecVal* ov)
{
    /* Use the adaptor interface to generate the required opaque handle.*/
    return c_bitvec_sv31a(svMakeBitPackedArrRef(iv), svMakeBitPackedArrRef(ov));
}

svLogic
c_logicvec(
    const svLogicVecVal* iv,
    svLogicVecVal* ov)
{
    /* Use the adaptor interface to generate the required opaque handle.*/
    return c_logicvec_sv31a(svMakeLogicPackedArrRef(iv), svMakeLogicPackedArrRef(ov));
}
