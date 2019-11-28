#include "dpiheader.h" 
#include "vpi_user.h" 


/*
 * This example shows how to use the DPI open array interfaces to read/write 
 * the open arrays of various kinds via DPI import routines. The example 
 * includes the usage of the open arrays with different element types, with
 * multiple unsized unpacked dimensions, and with a mixed unpacked dimensions
 * of both sized and unsized.
 */

/*
 * A simple utility routine that queries the array information
 * via the open array handle.
 */
static void
array_query(const char* str, const svOpenArrayHandle hin)
{
    int dim, count = svDimensions(hin);

    for (dim = count; dim > 0; --dim) {
       int left  =  svLeft(hin, dim);
       int right =  svRight(hin, dim);
       int low   =  svLow(hin, dim);
       int high  =  svHigh(hin, dim);
       int incr  =  svIncrement(hin, dim);
       int size  =  svSize(hin, dim);

       vpi_printf("%s: dim:%d, incr:%d, size:%d, left:%d, right:%d, low:%d, high:%d \n",
          str, dim, incr, size, left, right, low, high);
    }
}


/*
 * Copy all the open array elements of struct type from input open array to output open array
 * by traversing the array elements. It uses the C pointer iterator to access all the elements
 */
void clone_struct_oarr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int count = svSize(hin, 1); 
    MyType *s = (MyType *)svGetArrayPtr(hin); 
    MyType *d = (MyType *)svGetArrayPtr(hout); 

    array_query("clone_struct_oarr", hin);

    if (s && d) { /* both arrays have C layout */ 

        /* an efficient solution using pointer arithmetic */ 
        while (count--) 
            *d++ = *s++; 
    }
}


/*
 * Copy all the open array elements of struct type from input open array to output open array
 * by a single memcpy() call. This is the most efficient way for the copying. But this assumes
 * that the underlying array elements are stored in contiguously allocated memory, which isn't
 * an LRM requirement and may not be implemented the same in all simulators.
 */
void clone_struct_oarr_memcpy(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int count = svSize(hin, 1); 
    MyType *s = (MyType *)svGetArrayPtr(hin); 
    MyType *d = (MyType *)svGetArrayPtr(hout); 

    if (s && d) { /* both arrays have C layout */ 
        /* even more efficient: */
        memcpy(d, s, svSizeOfArray(hin)); 
    }
}


/*
 * Copy all the open array elements of struct type from input open array to output open array
 * by accessing each element using the standard interface svGetArrElemPtr1(). This is the
 * most portable approach and thus always safe to use.
 */
void clone_struct_oarr_safe(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int count = svSize(hin, 1); 
    MyType *s = (MyType *)svGetArrayPtr(hin); 
    MyType *d = (MyType *)svGetArrayPtr(hout); 

    if (s && d) { /* both arrays have C layout */ 
        int i = svLeft(hin, 1); 
        int j = svLeft(hout, 1); 
        int incr_i;
        int incr_j;

        if (i == svLow(hin, 1)) {
            incr_i = 1;
        } else {
            incr_i = 0;
        }

        if (j == svLow(hin, 1)) {
            incr_j = 1;
        } else {
            incr_j = 0;
        }

        while (1) { 
            *(MyType *)svGetArrElemPtr1(hout, j) = *(MyType *)svGetArrElemPtr1(hin, i); 
            if (i == svRight(hin, 1)) {
                break;
            }
            i = incr_i ? i + 1 : i - 1;
            j = incr_j ? j + 1 : j - 1;
        } 
    }  
} 


/*
 * Clone all the open array elements of svBitVecVal* type from input open array to output open array
 * using svGetArrElemPtr1()
 */
void clone_bitvec_oarr_by_elemptr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 1;

    int count = svSize(hin, dim); 
    svBitVecVal* s = (svBitVecVal*) svGetArrayPtr(hin); 
    svBitVecVal* d = (svBitVecVal*) svGetArrayPtr(hout); 

    array_query("clone_bitvec_oarr_by_elemptr", hin);

    if (s && d) { /* both arrays have C layout */ 
        int i = svLeft(hin, dim); 
        int j = svLeft(hout, dim); 
        int incr_i;
        int incr_j;
        if (i == svLow(hin, dim)) {
            incr_i = 1;
        } else {
            incr_i = 0;
        }
        if (j == svLow(hout, dim)) {
            incr_j = 1;
        } else {
            incr_j = 0;
        }
        while (1) { 
            s = (svBitVecVal*)svGetArrElemPtr1(hin, i); 
            svPutBitArrElem1VecVal(hout, s, j);
            if (i == svRight(hin, dim)) {
                break;
            }
            i = incr_i ? i + 1 : i - 1;
            j = incr_j ? j + 1 : j - 1;
        }
    }
}


/*
 * Clone all the open array elements of svBitVecVal* type from input open array to output open array
 * using svGetBitArrElem1VecVal()
 */
void clone_bitvec_oarr_by_elemval(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 1;
    svBitVecVal s;
    int i = svLeft(hin, dim); 
    int j = svLeft(hout, dim); 
    int incr_i;
    int incr_j;
    if (i == svLow(hin, dim)) {
        incr_i = 1;
    } else {
        incr_i = 0;
    }
    if (j == svLow(hout, dim)) {
        incr_j = 1;
    } else {
        incr_j = 0;
    }
    while (1) { 
        svGetBitArrElem1VecVal(&s, hin, i);
        svPutBitArrElem1VecVal(hout, &s, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }
}


/*
 * Clone all the 2D open array elements of svBitVecVal* type from input open array to output open array
 * using svGetArrElemPtr2()
 */
void clone_bitvec_2D_oarr_by_elemptr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 2;

    int count = svSize(hin, dim); 
    svBitVecVal* s = (svBitVecVal*) svGetArrayPtr(hin); 
    svBitVecVal* d = (svBitVecVal*) svGetArrayPtr(hout); 

    array_query("clone_bitvec_2D_oarr_by_elemptr", hin);

    if (s && d) { /* both arrays have C layout */ 
        int i = svLeft(hin, dim);
        int incr_i;
        int j = svLeft(hout, dim);
        int incr_j;
        if (i == svLow(hin, dim)) {
            incr_i = 1;
        } else {
            incr_i = 0;
        }
        if (j == svLow(hout, dim)) {
            incr_j = 1;
        } else {
            incr_j = 0;
        }
        while (1) {
            s = (svBitVecVal*)svGetArrElemPtr2(hin, 0, i); 
            svPutBitArrElem2VecVal(hout, s, 0, j);
            if (i == svRight(hin, dim)) {
                break;
            }
            i = incr_i ? i + 1 : i - 1;
            j = incr_j ? j + 1 : j - 1;
        }
    }
}


/*
 * Clone all the 2D open array elements of svBitVecVal* type from input open array to output open array
 * using svGetBitArrElem2VecVal()
 */
void clone_bitvec_2D_oarr_by_elemval(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 2;
    svBitVecVal s;
    int i = svLeft(hin, dim); 
    int incr_i;
    int j = svLeft(hout, dim);
    int incr_j;
    if (j == svLow(hout, dim)) {
        incr_j = 1;
    } else {
        incr_j = 0;
    }
    if (i == svLow(hin, dim)) {
        incr_i = 1;
    } else {
        incr_i = 0;
    }
    while (1) {
        svGetBitArrElem2VecVal(&s, hin, 0, i);
        svPutBitArrElem2VecVal(hout, &s, 0, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }
}


/*
 * Clone all the 3D open array elements of svBitVecVal* type from input open array to output open array
 * using svGetArrElemPtr3()
 */
void clone_bitvec_3D_oarr_by_elemptr(const svOpenArrayHandle hin, const svOpenArrayHandle hout)
{ 
    int dim = 3;

    int count = svSize(hin, dim); 
    svBitVecVal* s = (svBitVecVal*) svGetArrayPtr(hin); 
    svBitVecVal* d = (svBitVecVal*) svGetArrayPtr(hout); 

    array_query("clone_bitvec_2D_oarr_by_elemptr", hin);

    if (s && d) { /* both arrays have C layout */ 
        int i = svLeft(hin, dim); 
        int incr_i;
        int j = svLeft(hout, dim);
        int incr_j;
        if (j == svLow(hout, dim)) {
            incr_j = 1;
        } else {
            incr_j = 0;
        }
        if (i == svLow(hin, dim)) {
            incr_i = 1;
        } else {
            incr_i = 0;
        }
        while (1) { 
            s = (svBitVecVal*)svGetArrElemPtr3(hin, 0, 0, i); 
            svPutBitArrElem3VecVal(hout, s, 0, 0, j);
            if (i == svRight(hin, dim)) {
                break;
            }
            i = incr_i ? i + 1 : i - 1;
            j = incr_j ? j + 1 : j - 1;
        }
    }
}


/*
 * Clone all the 3D open array elements of svBitVecVal* type from input open array to output open array
 * using svGetBitArrElem3VecVal()
 */
void clone_bitvec_3D_oarr_by_elemval(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 3;
    svBitVecVal s;
    int i = svLeft(hin, dim); 
    int incr_i;
    int j = svLeft(hout, dim);
    int incr_j;
    if (j == svLow(hout, dim)) {
    incr_j = 1;
    } else {
        incr_j = 0;
    }
    if (i == svLow(hin, dim)) {
    incr_i = 1;
    } else {
        incr_i = 0;
    }
    while (1) { 
        svGetBitArrElem3VecVal(&s, hin, 0, 0, i);
        svPutBitArrElem3VecVal(hout, &s, 0, 0, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }
}


/*
 * Clone all the open array elements of svLogicVecVal* type from input open array to output open array
 * using svGetArrElemPtr1()
 */
void clone_logicvec_oarr_by_elemptr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 1;

    int count = svSize(hin, dim); 
    svLogicVecVal* s = (svLogicVecVal*) svGetArrayPtr(hin); 
    svLogicVecVal* d = (svLogicVecVal*) svGetArrayPtr(hout); 

    array_query("clone_logicvec_oarr_by_elemptr", hin);

    if (s && d) { /* both arrays have C layout */ 
        int i = svLeft(hin, dim); 
        int incr_i;
        int j = svLeft(hout, dim);
        int incr_j;
        if (j == svLow(hout, dim)) {
            incr_j = 1;
        } else {
            incr_j = 0;
        }
        if (i == svLow(hin, dim)) {
            incr_i = 1;
        } else {
            incr_i = 0;
        }
        while (1) { 
            s = (svLogicVecVal*)svGetArrElemPtr1(hin, i); 
            svPutLogicArrElem1VecVal(hout, s, j);
           if (i == svRight(hin, dim)) {
                break;
            }
            i = incr_i ? i + 1 : i - 1;
            j = incr_j ? j + 1 : j - 1;
        }
    }
}


/*
 * Clone all the open array elements of svLogicVecVal* type from input open array to output open array
 * using svGetLogicArrElem1VecVal()
 */
void clone_logicvec_oarr_by_elemval(const svOpenArrayHandle hin, const svOpenArrayHandle hout)
{ 
    int dim = 1;
    svLogicVecVal s;
    int i = svLeft(hin, dim); 
    int incr_i;
    int j = svLeft(hout, dim);
    int incr_j;
    if (j == svLow(hout, dim)) {
        incr_j = 1;
    } else {
        incr_j = 0;
    }
    if (i == svLow(hin, dim)) {
        incr_i = 1;
    } else {
        incr_i = 0;
    }
    while (1) {
        svGetLogicArrElem1VecVal(&s, hin, i);
        svPutLogicArrElem1VecVal(hout, &s, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }
}


/*
 * Clone all the 2D open array elements of svLogicVecVal* type from input open array to output open array
 * using svGetArrElemPtr2()
 */
void clone_logicvec_2D_oarr_by_elemptr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 2;

    int count = svSize(hin, dim); 
    svLogicVecVal* s = (svLogicVecVal*) svGetArrayPtr(hin); 
    svLogicVecVal* d = (svLogicVecVal*) svGetArrayPtr(hout); 

    array_query("clone_logicvec_2D_oarr_by_elemptr", hin);

    if (s && d) { /* both arrays have C layout */ 
        int i = svLeft(hin, dim); 
        int incr_i;
        int j = svLeft(hout, dim);
        int incr_j;
        if (j == svLow(hout, dim)) {
            incr_j = 1;
        } else {
            incr_j = 0;
        }
        if (i == svLow(hin, dim)) {
            incr_i = 1;
        } else {
            incr_i = 0;
        }
        while (1) { 
            s = (svLogicVecVal*)svGetArrElemPtr2(hin, 0, i); 
            svPutLogicArrElem2VecVal(hout, s, 0, j);
            if (i == svRight(hin, dim)) {
                break;
            }
            i = incr_i ? i + 1 : i - 1;
            j = incr_j ? j + 1 : j - 1;
        }
    }
}


/*
 * Clone all the 2D open array elements of svLogicVecVal* type from input open array to output open array
 * using svGetLogicArrElem2VecVal()
 */
void clone_logicvec_2D_oarr_by_elemval(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 2;
    svLogicVecVal s;
    int i = svLeft(hin, dim); 
    int incr_i;
    int j = svLeft(hout, dim);
    int incr_j;
    if (j == svLow(hout, dim)) {
        incr_j = 1;
    } else {
        incr_j = 0;
    }
    if (i == svLow(hin, dim)) {
        incr_i = 1;
    } else {
        incr_i = 0;
    }
    while (1) {
        svGetLogicArrElem2VecVal(&s, hin, 0, i);
        svPutLogicArrElem2VecVal(hout, &s, 0, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }
}


/*
 * Clone all the 3D open array elements of svLogicVecVal* type from input open array to output open array
 * using svGetArrElemPtr3()
 */
void clone_logicvec_3D_oarr_by_elemptr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 3;

    int count = svSize(hin, dim); 
    svLogicVecVal* s = (svLogicVecVal*) svGetArrayPtr(hin); 
    svLogicVecVal* d = (svLogicVecVal*) svGetArrayPtr(hout); 

    array_query("clone_logicvec_3D_oarr_by_elemptr", hin);

    if (s && d) { /* both arrays have C layout */ 
        int i = svLeft(hin, dim); 
        int incr_i;
        int j = svLeft(hout, dim);
        int incr_j;
        if (j == svLow(hout, dim)) {
            incr_j = 1;
        } else {
            incr_j = 0;
        }
        if (i == svLow(hin, dim)) {
            incr_i = 1;
        } else {
            incr_i = 0;
        }
        while (1) { 
            s = (svLogicVecVal*)svGetArrElemPtr3(hin, 0, 0, i); 
            svPutLogicArrElem3VecVal(hout, s, 0, 0, j);
            if (i == svRight(hin, dim)) {
                break;
            }
            i = incr_i ? i + 1 : i - 1;
            j = incr_j ? j + 1 : j - 1;
        }
    }
}


/*
 * Clone all the 3D open array elements of svLogicVecVal* type from input open array to output open array
 * using svGetLogicArrElem3VecVal()
 */
void clone_logicvec_3D_oarr_by_elemval(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 3;
    svLogicVecVal s;
    int i = svLeft(hin, dim); 
    int incr_i;
    int j = svLeft(hout, dim);
    int incr_j;
    if (j == svLow(hout, dim)) {
        incr_j = 1;
    } else {
        incr_j = 0;
    }
    if (i == svLow(hin, dim)) {
        incr_i = 1;
    } else {
        incr_i = 0;
    }
    while (1) {
        svGetLogicArrElem3VecVal(&s, hin, 0, 0, i);
        svPutLogicArrElem3VecVal(hout, &s, 0, 0, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }
}


/*
 * Clone all the open array elements of svBit type from input open array to output open array
 */
void clone_bit_oarr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 1;
    svBit s;
    int i = svLeft(hin, dim); 
    int incr_i;
    int j = svLeft(hout, dim);
    int incr_j;
    if (j == svLow(hout, dim)) {
        incr_j = 1;
    } else {
        incr_j = 0;
    }
    array_query("clone_bit_oarr", hin);
    if (i == svLow(hin, dim)) {
        incr_i = 1;
    } else {
        incr_i = 0;
    }
    while (1) {
        s = svGetBitArrElem1(hin, i);
        svPutBitArrElem1(hout, s, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }    
}


/*
 * Clone all the 2D open array elements of svBit type from input open array to output open array
 */
void clone_bit_2D_oarr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 2;
    svBit s;
    int i = svLeft(hin, dim); 
    int incr_i;
    int j = svLeft(hout, dim);
    int incr_j;
    if (j == svLow(hout, dim)) {
        incr_j = 1;
    } else {
        incr_j = 0;
    }
    if (i == svLow(hin, dim)) {
        incr_i = 1;
    } else {
        incr_i = 0;
    }
    while (1) {
        s = svGetBitArrElem2(hin, 0, i);
        svPutBitArrElem2(hout, s, 0, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }    
}


/*
 * Clone all the 3D open array elements of svBit type from input open array to output open array
 */
void clone_bit_3D_oarr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 3;
    svBit s;
    int i = svLeft(hin, dim); 
    int incr_i;
    int j = svLeft(hout, dim);
    int incr_j;
    if (j == svLow(hout, dim)) {
        incr_j = 1;
    } else {
        incr_j = 0;
    }
    if (i == svLow(hin, dim)) {
        incr_i = 1;
    } else {
        incr_i = 0;
    }
    while (1) {
        s = svGetBitArrElem3(hin, 0, 0, i);
        svPutBitArrElem3(hout, s, 0, 0, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }    
}


/*
 * Clone all the open array elements of svLogic type from input open array to output open array
 */
void clone_logic_oarr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 1;
    svLogic s;
    int i = svLeft(hin, dim); 
    int incr_i;
    int j = svLeft(hout, dim);
    int incr_j;
    if (j == svLow(hout, dim)) {
        incr_j = 1;
    } else {
        incr_j = 0;
    }
    array_query("clone_logic_oarr", hin);
    if (i == svLow(hin, dim)) {
        incr_i = 1;
    } else {
        incr_i = 0;
    }
    while (1) {
        s = svGetLogicArrElem1(hin, i);
        svPutLogicArrElem1(hout, s, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }    
}


/*
 * Clone all the 2D open array elements of svLogic type from input open array to output open array
 */
void clone_logic_2D_oarr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 2;
    svLogic s;
    int i = svLeft(hin, dim); 
    int incr_i;
    int j = svLeft(hout, dim);
    int incr_j;
    if (j == svLow(hout, dim)) {
        incr_j = 1;
    } else {
        incr_j = 0;
    }
    if (i == svLow(hin, dim)) {
        incr_i = 1;
    } else {
        incr_i = 0;
    }
    while (1) {
        s = svGetLogicArrElem2(hin, 0, i);
        svPutLogicArrElem2(hout, s, 0, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }    
}


/*
 * Clone all the 3D open array elements of svLogic type from input open array to output open array
 */
void clone_logic_3D_oarr(const svOpenArrayHandle hin, const svOpenArrayHandle hout) 
{ 
    int dim = 3;
    svLogic s;
    int i = svLeft(hin, dim); 
    int incr_i;
    int j = svLeft(hout, dim);
    int incr_j;
    if (j == svLow(hout, dim)) {
        incr_j = 1;
    } else {
        incr_j = 0;
    }
    if (i == svLow(hin, dim)) {
        incr_i = 1;
    } else {
        incr_i = 0;
    }
    while (1) {
        s = svGetLogicArrElem3(hin, 0, 0, i);
        svPutLogicArrElem3(hout, s, 0, 0, j);
        if (i == svRight(hin, dim)) {
            break;
        }
        i = incr_i ? i + 1 : i - 1;
        j = incr_j ? j + 1 : j - 1;
    }    
}
