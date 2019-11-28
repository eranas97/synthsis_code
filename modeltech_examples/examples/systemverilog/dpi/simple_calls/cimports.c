/*
 * DPI C functions for simple_dpi test.
 * These are just transparent wrappers around SV TF calls.
 */

#include "vpi_user.h"
#include "cimports.h"


DPI_DLLESPEC
int CFunction(
    int mcd,
    int level,
    int i1)
{
    int i;
    for (i = 0; i < level; i++)
        vpi_mcd_printf(mcd, "   ");

    vpi_mcd_printf(mcd, "In CFunction\n");
    return SVFunction(level + 1, i1);
}


DPI_DLLESPEC
int CTask(
    int mcd,
    int level,
    int i1,
    int i2,
    int *o1,
    int *o2,
    int *io1)
{
    int i;
    for (i = 0; i < level; i++)
        vpi_mcd_printf(mcd, "   ");

    vpi_mcd_printf(mcd, "In CTask\n");
    return SVTask(level + 1, i1, i2, o1, o2, io1);
}


