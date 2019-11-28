//
// Simple example that shows how to reuse existing SV3.1a DPI C code in a P1800-compliant fashion.
//

module top;

//
// DPI Spec String should be "DPI-C". "DPI" as defined in Accellera SV3.1a standard is not
// supported. This example shows two functions (c_bitvec() and c_logicvec()) that were
// originally written with "DPI" using the SV3.1a API. We have rewritten those two
// functions in such a way that the original C code is preserved, with the addition of
// some simple helper functions.
//

import "DPI-C" context function longint c_bitvec(input bit [63:0] iv, output bit [63:0] ov);

import "DPI-C" context function logic   c_logicvec(input logic [63:0] iv, output logic [63:0] ov);

initial begin
     bit [63:0]    bitarr;
     logic [63:0]  logicarr;
     longint       bret;
     logic         lret;

     bret = c_bitvec(64'hffff0000ffff0000, bitarr);
     $display("bitarr = %h", bitarr);
     assert(bret == bitarr) else $fatal();

     lret = c_logicvec(64'h55zzzz5555xxxx50, logicarr);
     $display("logicarr = %h", logicarr);
     assert(lret == logicarr[0]) else $fatal();
end

endmodule
