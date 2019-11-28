`timescale 1ns/1ps

`celldefine
module LS_HL (input I, output Z);
    buf (Z, I);
    specify
        (I => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module LS_LH (input I, output Z);
    buf (Z, I);
    specify
        (I => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine
