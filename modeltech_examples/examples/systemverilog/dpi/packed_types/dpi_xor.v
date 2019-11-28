module top;

typedef logic [63:0] lv64;
typedef bit [63:0] bv64;
typedef longint unsigned ulongint;

import "DPI-C" function void xor_longint(output ulongint z, input ulongint i0, i1);
import "DPI-C" function void xor_logicvec64(output lv64 z, input lv64 i0, i1);
import "DPI-C" function void xor_bitvec64(output bv64 z, input bv64 i0, i1);

lv64 flipper = 64'hffff0000ffff0000;
lv64 flippee = 64'h55zzzz5555xxxx55;
lv64 answer_4st;
bv64 answer_2st;

int mcd;

initial begin
    
    mcd = $fopen("results.txt") | 1;

    $fdisplay(mcd, "");
    $fdisplay(mcd, "Input #1       => %x", flippee);
    $fdisplay(mcd, "Input #2       => %x", flipper);
    $fdisplay(mcd, "");

    answer_4st = flippee ^ flipper;
    $fdisplay(mcd, "4-state answer => %x", answer_4st);
    
    xor_logicvec64(answer_4st, flippee, flipper);
    $fdisplay(mcd, "xor_logicvec64 => %x", answer_4st);
    $fdisplay(mcd, "");

    answer_2st = ulongint'(flippee) ^ ulongint'(flipper);
    $fdisplay(mcd, "2-state answer => %x", answer_2st);

    xor_longint(answer_2st, flippee, flipper);
    $fdisplay(mcd, "xor_longint    => %x", answer_2st);

    xor_bitvec64(answer_2st, flippee, flipper);
    $fdisplay(mcd, "xor_bitvec64   => %x", answer_2st);
    $fdisplay(mcd, "");

    $fclose(mcd);

end

endmodule
