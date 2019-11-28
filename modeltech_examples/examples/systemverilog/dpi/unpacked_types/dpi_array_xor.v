module top;

typedef logic [63:0] array_4st_6416 [16];
typedef bit [63:0] array_2st_6416 [16];
typedef longint unsigned ulongint;
typedef ulongint array_longint16 [16];

import "DPI-C" function void xor_4st_6416(output logic [63:0] z, input array_4st_6416 i);
import "DPI-C" function void xor_2st_6416(output bit [63:0] z, input array_2st_6416 i);
import "DPI-C" function void xor_2st_6416a(output bit [63:0] z, input bit [63:0] i [16]);
import "DPI-C" function void xor_longint16(output ulongint z, input array_longint16 i);

int mcd;
array_4st_6416 a4st;
array_2st_6416 a2st;
array_longint16 ali;

bit   [63:0] bitval;
logic [63:0] logicval;

initial begin
    
    mcd = $fopen("results.txt") | 1;

    for (int i = 0; i < 16; i++) begin
        a4st[i] = '0;
    end

    xor_4st_6416(logicval, a4st);
    $fdisplay(mcd, "4-state vector answer 0 => %x", logicval);

    xor_2st_6416(bitval, a2st);
    $fdisplay(mcd, "2-state vector answer 0 => %x", bitval);
    
    xor_2st_6416a(bitval, a2st);
    $fdisplay(mcd, "2-state vector answer 0 => %x", bitval);
    
    xor_longint16(bitval, ali);
    $fdisplay(mcd, "       longint answer 0 => %x", bitval);

    for (int i = 0; i < 16; i++) begin
        a4st[i] = '1;
        a2st[i] = '1;
        ali[i] = '1;
    end
    $fdisplay(mcd, "");

    xor_4st_6416(logicval, a4st);
    $fdisplay(mcd, "4-state vector answer 1 => %x", logicval);

    xor_2st_6416(bitval, a2st);
    $fdisplay(mcd, "2-state vector answer 1 => %x", bitval);
    
    xor_2st_6416a(bitval, a2st);
    $fdisplay(mcd, "2-state vector answer 1 => %x", bitval);
    
    xor_longint16(bitval, ali);
    $fdisplay(mcd, "       longint answer 1 => %x", bitval);

    for (int i = 0; i < 16; i++) begin
        a4st[i] = 'h100000001 << i;
        a2st[i] = 'h100000001 << i;
        ali[i] = 'h100000001 << i;
    end
    $fdisplay(mcd, "");

    xor_4st_6416(logicval, a4st);
    $fdisplay(mcd, "4-state vector answer 2 => %x", logicval);

    xor_2st_6416(bitval, a2st);
    $fdisplay(mcd, "2-state vector answer 2 => %x", bitval);
    
    xor_2st_6416a(bitval, a2st);
    $fdisplay(mcd, "2-state vector answer 2 => %x", bitval);
    
    xor_longint16(bitval, ali);
    $fdisplay(mcd, "       longint answer 2 => %x", bitval);

    $fclose(mcd);

end

endmodule
