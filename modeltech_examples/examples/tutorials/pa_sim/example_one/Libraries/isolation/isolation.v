`timescale 1ns/1ps

`celldefine
module ISO_LO (input ISO, I, output Z);
    not (im0, ISO);
    nand (im1, im0, I);
    not (Z, im1);
    specify
        (I => Z) = (0, 0);
        (ISO => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine

`celldefine
module ISO_HI (input ISO, I, output Z);
    or (Z, I, ISO);
    specify
        (I => Z) = (0, 0);
        (ISO => Z) = (0, 0);
    endspecify
endmodule
`endcelldefine