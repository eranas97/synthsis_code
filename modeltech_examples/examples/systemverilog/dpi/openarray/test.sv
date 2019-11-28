module top;

    // **************************************************************
    // This example shows how to use the DPI open array interfaces to read/write 
    // open arrays of various kinds via DPI import routines. The example 
    // includes usage of open arrays with different element types, with
    // multiple unsized unpacked dimensions, and with mixed unpacked dimensions
    // of both sized and unsized.
    // **************************************************************

    // typedef for unpacked struct, which will be used as the type of open array element
    typedef struct { 
        bit   [11:0] x;
        logic [0:11] y;
    } MyType; 

    // typedef for logic vector with different number of unpacked dimensions
    typedef logic[3:0]  My1DLV[5:0];
    typedef logic[3:0]  My2DLV[7:0][5:0];
    typedef logic[0:3]  My3DLV[11:0][7:0][5:0];

    // typedef for bit vector with different number of unpacked dimensions
    typedef bit[3:0]  My1DBV[5:0];
    typedef bit[3:0]  My2DBV[7:0][5:0];
    typedef bit[0:3]  My3DBV[11:0][7:0][5:0];

    // typedef for bit scalar with different number of unpacked dimensions
    typedef bit  My1DBS[5:0];
    typedef bit  My2DBS[7:0][5:0];
    typedef bit  My3DBS[11:0][7:0][5:0];

    // typedef for logic scalar with different number of unpacked dimensions
    typedef logic  My1DLS[5:0];
    typedef logic  My2DLS[7:0][5:0];
    typedef logic  My3DLS[11:0][7:0][5:0];

    // **************************************************************
    // Unpacked struct open array related DPI import declarations
    // **************************************************************

    // There are multiple import routines that are functionally equivalent, for example, the
    // following three variations of clone_struct_oarr(). These are intended to demonstrate
    // the different implementation choices on the C side.

    // The corresponding C implementation demonstrates a typical C pointer iterator-like 
    // way of accessing the open array elements.

    import "DPI-C" function void clone_struct_oarr(input MyType i [], output MyType o []); 

    // The corresponding C implementation is the most efficient one as it uses a single
    // memcpy() call to copy the array elements from source to desitnation. This however requires
    // that the open array elements are layed out in contiguous memory allocations in the 
    // tool implemention.

    import "DPI-C" function void clone_struct_oarr_memcpy(input MyType i [], output MyType o []);

    // The corresponding C implementation is most portable as it makes no assumption that
    // the underlying layout of open array elements are arranged in a contiguous allocation.

    import "DPI-C" function void clone_struct_oarr_safe(input MyType i [], output MyType o []); 

    // **************************************************************
    // bit/logic vector open array related DPI imports
    // **************************************************************

    // Shows how to access the elements of bit vector type using the element pointer interface.

    import "DPI-C" function void clone_bitvec_oarr_by_elemptr(input bit[] i [], output bit[] o []);

    // Shows how to access the elements of bit vector type using the direct element value fetching interface.

    import "DPI-C" function void clone_bitvec_oarr_by_elemval(input bit[] i [], output bit[] o []); 

    // Shows how to use the open arrays of bit vectors with all dimensions (both packed and unpacked)
    // being unsized dimensions. 
    // The first one uses the pointer interface to access element values.
    // The second one uses the direct value fetching interface.

    import "DPI-C" function void clone_bitvec_2D_oarr_by_elemptr(input bit[] i [][], output bit[] o [][]); 
    import "DPI-C" function void clone_bitvec_2D_oarr_by_elemval(input bit[] i [][], output bit[] o [][]); 

    // Shows how to use the open arrays of bit vectors with unpacked dimensions being a mix of
    // both sized and unsized.
    // The first one uses the pointer interface to access element values.
    // The second one uses the direct value fetching interface.

    import "DPI-C" function void clone_bitvec_3D_oarr_by_elemptr(input bit[3:0] i [][8][], output bit[3:0] o [][][6]); 
    import "DPI-C" function void clone_bitvec_3D_oarr_by_elemval(input bit[3:0] i [12][][], output bit[3:0] o [][8][]); 

    // Shows how to access the element of logic vector type using the element pointer interface.

    import "DPI-C" function void clone_logicvec_oarr_by_elemptr(input logic[] i [], output logic[] o []); 

    // Shows how to access the element of logic  vector type using the direct element value fetching interface.

    import "DPI-C" function void clone_logicvec_oarr_by_elemval(input logic[] i [], output logic[] o []); 

    // Shows how to use the open arrays of logic vectors with all dimensions (both packed and unpacked)
    // being unsized dimensions. 
    // The first one uses the pointer interface to access element values.
    // The second one uses the direct value fetching interface.

    import "DPI-C" function void clone_logicvec_2D_oarr_by_elemptr(input logic[] i [][], output logic[] o [][]); 
    import "DPI-C" function void clone_logicvec_2D_oarr_by_elemval(input logic[] i [][], output logic[] o [][]); 

    // Shows how to use the open arrays of logic vectors with unpacked dimensions being a mix of
    // both sized and unsized.
    // The first one uses the pointer interface to access element values.
    // The second one uses the direct value fetching interface.

    import "DPI-C" function void clone_logicvec_3D_oarr_by_elemptr(input logic[3:0] i [][8][], output logic[3:0] o [][][6]); 
    import "DPI-C" function void clone_logicvec_3D_oarr_by_elemval(input logic[3:0] i [12][][], output logic[3:0] o [][8][]); 

    // **************************************************************
    // scalar open array related DPI imports
    // **************************************************************

    // Shows how to use a simple open arrays of bit scalars.
    import "DPI-C" function void clone_bit_oarr(input bit[] i [], output bit[] o []); 

    // Shows how to use the open arrays of bit scalars with all dimensions (both packed and unpacked)
    // being unsized dimensions. 

    import "DPI-C" function void clone_bit_2D_oarr(input bit[] i [][], output bit[] o [][]); 

    // Shows how to use the open arrays of bit scalars with unpacked dimensions being a mix of
    // both sized and unsized.

    import "DPI-C" function void clone_bit_3D_oarr(input bit[] i [][8][], output bit[] o [][][6]); 

    // Shows how to use a simple open arrays of logic scalars.

    import "DPI-C" function void clone_logic_oarr(input logic[] i [], output logic[] o []); 

    // Shows how to use the open arrays of logic scalars with all dimensions (both packed and unpacked)
    // being unsized dimensions. 

    import "DPI-C" function void clone_logic_2D_oarr(input logic[] i [][], output logic[] o [][]); 

    // Shows how to use the open arrays of logic scalars with unpacked dimensions being a mix of
    // both sized and unsized.

    import "DPI-C" function void clone_logic_3D_oarr(input logic[] i [12][][], output logic[] o [][8][]); 

    // *****************************************************************
    // Begin SV array declaration. They will be used as actual arguments
    // of DPI import calls. 
    // *****************************************************************
    MyType source [11:20] = '{'{1, 9}, '{2, 8}, '{3, 7}, '{4, 6}, '{5, 5}, '{6, 4}, '{7, 3}, '{8, 2}, '{9, 1}, '{0, 10}} ; 
    MyType target [11:20]; 

    My1DLV lv1d, lv1d_o;
    My2DLV lv2d, lv2d_o;
    My3DLV lv3d, lv3d_o;

    My1DBV bv1d, bv1d_o;
    My2DBV bv2d, bv2d_o;
    My3DBV bv3d, bv3d_o;

    My1DBS bs1d, bs1d_o;
    My2DBS bs2d, bs2d_o;
    My3DBS bs3d, bs3d_o;
    My1DLS ls1d, ls1d_o;
    My2DLS ls2d, ls2d_o;
    My3DLS ls3d, ls3d_o;

    // **************************************************************
    // End SV array declaration. 
    // **************************************************************


    initial begin
        int i;

        // ***************************************************************
        // The SV arrays are all initialized to trivially known values for
        // the purpose of easy checking of the results.
        // ***************************************************************
        for (i = 0; i < 6; ++i) begin
             lv1d[i] = i+3;
             lv2d[0][i] = i+3;
             lv3d[0][0][i] = i+3;

             bv1d[i] = i+3;
             bv2d[0][i] = i+3;
             bv3d[0][0][i] = i+3;

             if (i == 0) begin
                 bs1d[i] = 0;
                 bs2d[0][i] = 0;
                 bs3d[0][0][i] = 0;

                 ls1d[i] = 1;
                 ls2d[0][i] = 1;
                 ls3d[0][0][i] = 1;
             end else begin
                 bs1d[i] = !bs1d[i-1];
                 bs2d[0][i] = !bs2d[0][i-1];
                 bs3d[0][0][i] = !bs3d[0][0][i-1];

                 ls1d[i] = !ls1d[i-1];
                 ls2d[0][i] = !ls2d[0][i-1];
                 ls3d[0][0][i] = !ls3d[0][0][i-1];
             end
        end

        // **************************************************************
        // The following procedural code in the iniital block simply calls
        // the DPI import routines previously declared one by one. The
        // $display output shows both the expected result and the actual result.
        // **************************************************************
        clone_struct_oarr(source, target); 
        $display("clone_struct_oarr: %p", target);

        clone_struct_oarr_memcpy(source, target); 
        $display("clone_struct_oarr_memcpy: %p", target);

        clone_struct_oarr_safe(source, target); 
        $display("clone_struct_oarr_safe: %p", target);
  
        clone_bitvec_oarr_by_elemptr(bv1d, bv1d_o);   
        $display("clone_bitvec_oarr_by_elemptr: %p, expecting %p", bv1d_o, bv1d);

        clone_bitvec_oarr_by_elemval(bv1d, bv1d_o);   
        $display("clone_bitvec_oarr_by_elemval: %p, expecting %p", bv1d_o, bv1d);

        clone_bitvec_2D_oarr_by_elemptr(bv2d, bv2d_o);   
        $display("clone_bitvec_2D_oarr_by_elemptr: %p, expecting %p", bv2d_o[0], bv2d[0]);

        clone_bitvec_2D_oarr_by_elemval(bv2d, bv2d_o);   
        $display("clone_bitvec_2D_oarr_by_elemval: %p, expecting %p", bv2d_o[0], bv2d[0]);

        clone_bitvec_3D_oarr_by_elemptr(bv3d, bv3d_o);   
        $display("clone_bitvec_3D_oarr_by_elemptr: %p, expecting %p", bv3d_o[0][0], bv3d[0][0]);

        clone_bitvec_3D_oarr_by_elemval(bv3d, bv3d_o);   
        $display("clone_bitvec_3D_oarr_by_elemval: %p, expecting %p", bv3d_o[0][0], bv3d[0][0]);

        clone_logicvec_oarr_by_elemptr(lv1d, lv1d_o);   
        $display("clone_logicvec_oarr_by_elemptr: %p, expecting %p", lv1d_o, lv1d);

        clone_logicvec_oarr_by_elemval(lv1d, lv1d_o);   
        $display("clone_logicvec_oarr_by_elemval: %p, expecting %p", lv1d_o, lv1d);

        clone_logicvec_2D_oarr_by_elemptr(lv2d, lv2d_o);   
        $display("clone_logicvec_2D_oarr_by_elemptr: %p, expecting %p", lv2d_o[0], lv2d[0]);

        clone_logicvec_2D_oarr_by_elemval(lv2d, lv2d_o);   
        $display("clone_logicvec_2D_oarr_by_elemval: %p, expecting %p", lv2d_o[0], lv2d[0]);

        clone_logicvec_3D_oarr_by_elemptr(lv3d, lv3d_o);   
        $display("clone_logicvec_3D_oarr_by_elemptr: %p, expecting %p", lv3d_o[0][0], lv3d[0][0]);

        clone_logicvec_3D_oarr_by_elemval(lv3d, lv3d_o);   
        $display("clone_logicvec_3D_oarr_by_elemval: %p, expecting %p", lv3d_o[0][0], lv3d[0][0]);

        clone_bit_oarr(bs1d, bs1d_o);   
        $display("clone_bit_oarr: %p, expecting %p", bs1d_o, bs1d);

        clone_bit_2D_oarr(bs2d, bs2d_o);   
        $display("clone_bit_2D_oarr: %p, expecting %p", bs2d_o[0], bs2d[0]);

        clone_bit_3D_oarr(bs3d, bs3d_o);   
        $display("clone_bit_3D_oarr: %p, expecting %p", bs3d_o[0][0], bs3d[0][0]);

        clone_logic_oarr(ls1d, ls1d_o);   
        $display("clone_logic_oarr: %p, expecting %p", ls1d_o, ls1d);
    
        clone_logic_2D_oarr(ls2d, ls2d_o);   
        $display("clone_logic_2D_oarr: %p, expecting %p", ls2d_o[0], ls2d[0]);

        clone_logic_3D_oarr(ls3d, ls3d_o);   
        $display("clone_logic_3D_oarr: %p, expecting %p", ls3d_o[0][0], ls3d[0][0]);

    end
endmodule
